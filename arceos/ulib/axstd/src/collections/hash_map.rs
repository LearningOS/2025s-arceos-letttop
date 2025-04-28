use crate::rand::random;
use crate::string::String;
use crate::vec;
use crate::vec::Vec;
use core::hash::{BuildHasher, Hasher};

const DEFAULT_CAPACITY: usize = 4096;
const LOAD_FACTOR_NUM: usize = 3; // 分子
const LOAD_FACTOR_DEN: usize = 4; // 分母 —— 0.75

// Hasher struct
pub struct SimpleHasher {
    state: u64,
}

impl SimpleHasher {
    fn new(seed: u64) -> Self {
        SimpleHasher { state: seed }
    }
}

impl Hasher for SimpleHasher {
    fn finish(&self) -> u64 {
        self.state
    }

    fn write(&mut self, bytes: &[u8]) {
        // state = state *31 + b
        for &b in bytes {
            self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
        }
    }
}

// HashBuilder struct
// 存储seed
#[derive(Default, Copy, Clone)]
pub struct SimpleHashBuilder {
    seed: u64,
}

//
impl SimpleHashBuilder {
    pub fn new() -> Self {
        Self {
            seed: random() as u64,
        }
    }
}

impl BuildHasher for SimpleHashBuilder {
    type Hasher = SimpleHasher;

    fn build_hasher(&self) -> Self::Hasher {
        // 重复使用同一个seed
        SimpleHasher::new(self.seed)
    }
}

/// HashMap
/// 开地址 + 掩码索引 + 线性探测
pub struct HashMap {
    // buckets 存储值
    buckets: Vec<Option<(String, u32)>>,
    // mask 是 2^k-1，即低k位为1
    // hash & 2^k-1 == hash % 2^k
    mask: usize,
    build_hasher: SimpleHashBuilder,
    len: u64,
}

impl HashMap {
    pub fn with_build_hasher_and_capacity(build_hasher: SimpleHashBuilder, cap: usize) -> Self {
        assert!(cap.is_power_of_two(), "capacity must be a power of 2");
        Self {
            buckets: vec![None; cap],
            mask: cap - 1,
            build_hasher: build_hasher,
            len: 0,
        }
    }

    pub fn new() -> Self {
        Self::with_build_hasher_and_capacity(SimpleHashBuilder::new(), DEFAULT_CAPACITY)
    }

    /// 计算 key 的哈希值
    fn make_hash(&self, key: &String) -> u64 {
        let mut hasher = self.build_hasher.build_hasher();
        // 调用 SimpleHasher::write
        hasher.write(key.as_bytes());
        hasher.finish()
    }

    pub fn insert(&mut self, key: String, value: u32) {
        //
        let hash = self.make_hash(&key);
        let mut idx = (hash as usize) & self.mask;

        // 检查扩容
        if (self.len + 1) * LOAD_FACTOR_DEN as u64 > (self.buckets.len() * LOAD_FACTOR_NUM) as u64 {
            let new_cap = self.buckets.len() * 2;
            let mut new_map =
                HashMap::with_build_hasher_and_capacity(self.build_hasher.clone(), new_cap);
            for slot in self.buckets.iter_mut().filter_map(|s| s.take()) {
                let (k, v) = slot;
                new_map.insert(k, v);
            }
            *self = new_map;
        }

        //
        loop {
            match &mut self.buckets[idx] {
                // 碰到空桶，直接放下
                None => {
                    self.buckets[idx] = Some((key, value));
                    self.len += 1;
                    return;
                }
                // 如果 key 相同，就更新
                Some((existing_key, existing_val)) if existing_key == &key => {
                    *existing_val = value;
                    return;
                }
                // 冲突了，线性探测下一个位置
                _ => {
                    idx = (idx + 1) & self.mask;
                }
            }
        }
    }

    pub fn get(&self, key: String) -> Option<u32> {
        let hash = self.make_hash(&key);
        let mut idx = (hash as usize) & self.mask;

        loop {
            match &self.buckets[idx] {
                None => return None,
                Some((existing_key, ref existing_val)) if existing_key == &key => {
                    return Some(*existing_val);
                }
                // 冲突了，线性探测下一个位置
                _ => {
                    idx = (idx + 1) & self.mask;
                }
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &u32)> {
        self.buckets
            .iter()
            .filter_map(|slot| slot.as_ref().map(|(k, v)| (k, v)))
    }
}
