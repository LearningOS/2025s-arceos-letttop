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

    /// Rename a file or directory to a new name.
    /// Delete the original file if `old` already exists.
    ///
    /// This only works then the new path is in the same mounted fs.
    fn rename(&self, old: &str, new: &str) -> VfsResult {
        // log::info!("rename {} to {}", old, new);
        // rename /f1 to /tmp/f2

        // 对于本ramfs来说，就是挂载在/tmp下的
        // 以/tmp开始的就是绝对地址，取之后的
        // 以/其他开始的是错误
        // 其他为相对地址或文件
        //
        // 直接以self为root即可

        let ramfs_root_dir_node = self.this.upgrade().unwrap().clone();

        let (old_dir_path, old_file_name) = parse_path(old);
        let (new_dir_path, new_file_name) = parse_path(new);

        let old_dir_node = ramfs_root_dir_node.clone().lookup(&old_dir_path).unwrap();
        let new_dir_node = ramfs_root_dir_node.clone().lookup(&new_dir_path).unwrap();

        // 删除原来的文件，即从原父节点的children列表去掉
        let move_node = old_dir_node
            .as_any()
            .downcast_ref::<DirNode>()
            .expect("not a dir node")
            .children
            .write()
            .remove(&old_file_name)
            .ok_or(VfsError::NotFound)
            .expect("old file not find");

        // 加入新父节点的children列表
        new_dir_node
            .as_any()
            .downcast_ref::<DirNode>()
            .expect("not a dir node")
            .children
            .write()
            .insert(new_file_name, move_node.clone());

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

/// Parse a path into (directory_path, file_name) tuple.
/// Examples:
/// - "/f1" -> ("", "f1")
/// - "/tmp/f1" -> ("", "f1") if tmp is root
/// - "/tmp/dir1/f1" -> ("dir1", "f1")
/// - "f1" -> ("", "f1")
fn parse_path(path: &str) -> (String, String) {
    let path = path.trim_start_matches('/');

    // Handle empty path
    if path.is_empty() {
        return (String::new(), String::new());
    }

    let parts: Vec<&str> = path.split('/').collect();

    match parts.len() {
        0 => (String::new(), String::new()),
        1 => (String::new(), parts[0].into()),
        _ => {
            if parts[0] == "tmp" {
                // Remove "tmp" prefix if present
                match parts.len() {
                    2 => (String::new(), parts[1].into()),
                    _ => {
                        let dir_path: String = parts[1..parts.len() - 1].join("/").into();
                        let file_name: String = parts.last().map(|&s| s.into()).unwrap_or_default();
                        (dir_path, file_name)
                    }
                }
            } else {
                let dir_path: String = parts[..parts.len() - 1].join("/").into();
                let file_name: String = parts.last().map(|&s| s.into()).unwrap_or_default();
                (dir_path, file_name)
            }
        }
    }
}
