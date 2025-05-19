use alloc::collections::BTreeMap;
use alloc::sync::{Arc, Weak};
use alloc::{string::String, vec::Vec};

use axfs_vfs::{VfsDirEntry, VfsNodeAttr, VfsNodeOps, VfsNodeRef, VfsNodeType};
use axfs_vfs::{VfsError, VfsResult};
use spin::RwLock;

use crate::file::FileNode;

/// The directory node in the RAM filesystem.
///
/// It implements [`axfs_vfs::VfsNodeOps`].
pub struct DirNode {
    this: Weak<DirNode>,
    parent: RwLock<Weak<dyn VfsNodeOps>>,
    children: RwLock<BTreeMap<String, VfsNodeRef>>,
}

impl DirNode {
    pub(super) fn new(parent: Option<Weak<dyn VfsNodeOps>>) -> Arc<Self> {
        Arc::new_cyclic(|this| Self {
            this: this.clone(),
            parent: RwLock::new(parent.unwrap_or_else(|| Weak::<Self>::new())),
            children: RwLock::new(BTreeMap::new()),
        })
    }

    pub(super) fn set_parent(&self, parent: Option<&VfsNodeRef>) {
        *self.parent.write() = parent.map_or(Weak::<Self>::new() as _, Arc::downgrade);
    }

    /// Returns a string list of all entries in this directory.
    pub fn get_entries(&self) -> Vec<String> {
        self.children.read().keys().cloned().collect()
    }

    /// Checks whether a node with the given name exists in this directory.
    pub fn exist(&self, name: &str) -> bool {
        self.children.read().contains_key(name)
    }

    /// Creates a new node with the given name and type in this directory.
    pub fn create_node(&self, name: &str, ty: VfsNodeType) -> VfsResult {
        if self.exist(name) {
            log::error!("AlreadyExists {}", name);
            return Err(VfsError::AlreadyExists);
        }
        let node: VfsNodeRef = match ty {
            VfsNodeType::File => Arc::new(FileNode::new()),
            VfsNodeType::Dir => Self::new(Some(self.this.clone())),
            _ => return Err(VfsError::Unsupported),
        };
        self.children.write().insert(name.into(), node);
        Ok(())
    }

    /// Removes a node by the given name in this directory.
    pub fn remove_node(&self, name: &str) -> VfsResult {
        let mut children = self.children.write();
        let node = children.get(name).ok_or(VfsError::NotFound)?;
        if let Some(dir) = node.as_any().downcast_ref::<DirNode>() {
            if !dir.children.read().is_empty() {
                return Err(VfsError::DirectoryNotEmpty);
            }
        }
        children.remove(name);
        Ok(())
    }
}

impl VfsNodeOps for DirNode {
    fn get_attr(&self) -> VfsResult<VfsNodeAttr> {
        Ok(VfsNodeAttr::new_dir(4096, 0))
    }

    fn parent(&self) -> Option<VfsNodeRef> {
        self.parent.read().upgrade()
    }

    fn lookup(self: Arc<Self>, path: &str) -> VfsResult<VfsNodeRef> {
        let (name, rest) = split_path(path);
        let node = match name {
            "" | "." => Ok(self.clone() as VfsNodeRef),
            ".." => self.parent().ok_or(VfsError::NotFound),
            _ => self
                .children
                .read()
                .get(name)
                .cloned()
                .ok_or(VfsError::NotFound),
        }?;

        if let Some(rest) = rest {
            node.lookup(rest)
        } else {
            Ok(node)
        }
    }

    fn read_dir(&self, start_idx: usize, dirents: &mut [VfsDirEntry]) -> VfsResult<usize> {
        let children = self.children.read();
        let mut children = children.iter().skip(start_idx.max(2) - 2);
        for (i, ent) in dirents.iter_mut().enumerate() {
            match i + start_idx {
                0 => *ent = VfsDirEntry::new(".", VfsNodeType::Dir),
                1 => *ent = VfsDirEntry::new("..", VfsNodeType::Dir),
                _ => {
                    if let Some((name, node)) = children.next() {
                        *ent = VfsDirEntry::new(name, node.get_attr().unwrap().file_type());
                    } else {
                        return Ok(i);
                    }
                }
            }
        }
        Ok(dirents.len())
    }

    fn create(&self, path: &str, ty: VfsNodeType) -> VfsResult {
        log::debug!("create {:?} at ramfs: {}", ty, path);
        let (name, rest) = split_path(path);
        if let Some(rest) = rest {
            match name {
                "" | "." => self.create(rest, ty),
                ".." => self.parent().ok_or(VfsError::NotFound)?.create(rest, ty),
                _ => {
                    let subdir = self
                        .children
                        .read()
                        .get(name)
                        .ok_or(VfsError::NotFound)?
                        .clone();
                    subdir.create(rest, ty)
                }
            }
        } else if name.is_empty() || name == "." || name == ".." {
            Ok(()) // already exists
        } else {
            self.create_node(name, ty)
        }
    }

    fn remove(&self, path: &str) -> VfsResult {
        log::debug!("remove at ramfs: {}", path);
        let (name, rest) = split_path(path);
        if let Some(rest) = rest {
            match name {
                "" | "." => self.remove(rest),
                ".." => self.parent().ok_or(VfsError::NotFound)?.remove(rest),
                _ => {
                    let subdir = self
                        .children
                        .read()
                        .get(name)
                        .ok_or(VfsError::NotFound)?
                        .clone();
                    subdir.remove(rest)
                }
            }
        } else if name.is_empty() || name == "." || name == ".." {
            Err(VfsError::InvalidInput) // remove '.' or '..
        } else {
            self.remove_node(name)
        }
    }

    // test use std::fs::rename directly, move shell rename to here
    // parent_node_of(None, old).rename(old, new)
    // so self here is parent node
    /// Rename a file or directory to a new name.
    /// Delete the original file if `old` already exists.
    ///
    /// This only works then the new path is in the same mounted fs.
    fn rename(&self, old: &str, new: &str) -> VfsResult {
        // log::info!("rename {} to {}", old, new);
        // rename /f1 to /tmp/f2

        let old_parent_node = self.this.upgrade().unwrap().clone();
        let a = Arc::as_ptr(&self.this.upgrade().unwrap());
        log::info!("the mainfs root dir is at = {:p}", a);
        for (name, _node) in old_parent_node.children.read().iter() {
            log::info!("the mainfs root dir has child:  {}", name);
        }

        let root: VfsNodeRef = {
            let mut current: VfsNodeRef = old_parent_node.clone();

            while let Some(parent) = current.parent() {
                current = parent;
            }
            current
        };

        let c = root.clone();
        let c = Arc::as_ptr(&c);
        log::info!("look up root is at {:p}", c);
        for (name, _node) in root
            .as_any()
            .downcast_ref::<DirNode>()
            .unwrap()
            .children
            .read()
            .iter()
        {
            log::info!("look up root has child:  {}", name);
        }

        let (new_dir_path, new_file_name) = split_path(new);
        // log::info!(
        //     "rename: new_dir_path: {}, new_file_name: {:#?}",
        //     new_dir_path,
        //     new_file_name
        // );
        let (path1, path2) = split_path(old);
        // log::info!("rename: old_dir_path {}, old_file_name {:#?}", path1, path2);
        let old_file_name = match path2 {
            Some(name) => name,
            None => path1,
        };
        // log::info!("rename: , old_file_name {:#?}", old_file_name);

        // 删除原来的文件
        let move_node = old_parent_node
            .clone()
            .lookup(old_file_name)
            .expect("old file not find");
        let b = Arc::as_ptr(&move_node);
        log::info!("old file is at = {:p}", b);

        //
        let new_parent_node = root
            .clone()
            .lookup(new_dir_path)
            .expect("get dir node failed, may have wrong new name");
        let b = Arc::as_ptr(&new_parent_node);
        log::info!("dir of new file is at = {:p}", b);
        for (name, _node) in new_parent_node
            .as_any()
            .downcast_ref::<DirNode>()
            .unwrap()
            .children
            .read()
            .iter()
        {
            log::info!("look up root has child:  {}", name);
        }

        // ?????????
        // [  0.413366 0 axfs_ramfs::dir:219] old_parent_node ptr = 0xffffffc080287820
        // [  0.415143 0 axfs_ramfs::dir:220] new_parent_node ptr = 0xffffffc0802878c0
        // let a = Arc::as_ptr(&old_parent_node);
        // log::info!("old_parent_node ptr = {:p}", a);

        //
        old_parent_node
            .as_any()
            .downcast_ref::<DirNode>()
            .expect("not a dir node")
            .children
            .write()
            .insert(new_file_name.unwrap().into(), move_node.clone());
        log::info!("rename: add new_file_name {:?}", new_file_name);
        Ok(())
    }

    axfs_vfs::impl_vfs_dir_default! {}

    fn open(&self) -> VfsResult {
        Ok(())
    }

    fn release(&self) -> VfsResult {
        Ok(())
    }
}

fn split_path(path: &str) -> (&str, Option<&str>) {
    let trimmed_path = path.trim_start_matches('/');
    trimmed_path.find('/').map_or((trimmed_path, None), |n| {
        (&trimmed_path[..n], Some(&trimmed_path[n + 1..]))
    })
}
