use arceos_api::modules::axhal::misc::random;

use crate::string::String;
use crate::vec::Vec;
use core::hash::{BuildHasher, Hasher};

// Hasher struct
pub struct SimpleHasher {
    state: u64,
}

impl Hasher for SimpleHasher {
    fn finish(&self) -> u64 {
        self.state
    }

    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
        }
    }
}

// HashBuilder struct
#[derive(Default)]
pub struct SimpleHashBuilder;

impl BuildHasher for SimpleHashBuilder {
    type Hasher = SimpleHasher;

    fn build_hasher(&self) -> Self::Hasher {
        SimpleHasher {
            state: random() as u64,
        }
    }
}

// HashMap
#[derive(Default)]
pub struct HashMap {
    entries: Vec<(String, u32)>,
    hasher: SimpleHashBuilder,
}

impl HashMap {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            hasher: SimpleHashBuilder,
        }
    }

    pub fn with_hasher() -> Self {
        Self::new()
    }

    pub fn insert(&mut self, key: String, value: u32) {
        // 简单实现：如果键已存在则更新值，否则添加新条目
        for entry in &mut self.entries {
            if entry.0 == key {
                entry.1 = value;
                return;
            }
        }
        self.entries.push((key, value));
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &u32)> {
        self.entries.iter().map(|(k, v)| (k, v))
    }
}
