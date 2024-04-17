use std::cell::Cell;

#[derive(Default)]
pub struct UnionFind {
    /// If `parents[i] == i`, then `i` is a root
    ///
    /// If `parents[i] == usize::MAX`, then `i` is not in the data structure.
    parents: Vec<Cell<usize>>,
}

impl UnionFind {
    /// Returns `true` if the key is newly added
    pub fn insert(&mut self, key: usize) -> bool {
        if let Some(parent) = self.parents.get_mut(key) {
            if parent.get() == usize::MAX {
                parent.set(key);
                true
            } else {
                false
            }
        } else {
            self.parents.resize_with(key + 1, || Cell::new(usize::MAX));
            self.parents[key].set(key);
            true
        }
    }

    /// Returns `None` if the key is not in the data structure
    pub fn strict_root_of(&self, key: usize) -> Option<usize> {
        let parent = self.parents.get(key)?;
        if parent.get() == key {
            return Some(key);
        } else if parent.get() == usize::MAX {
            return None;
        }
        let Some(root) = self.strict_root_of(parent.get()) else {
            unreachable!(
                "if a key is in the data structure, it's parent must also be"
            );
        };
        parent.set(root);
        Some(root)
    }

    pub fn root_of(&self, key: usize) -> usize {
        self.strict_root_of(key).unwrap_or(key)
    }

    /// Merges the sets containing the two keys.
    ///
    /// Inserts the keys if they were not previously in the data structure.
    ///
    /// Returns `true` if merging occurred, `false` if they keys were already in
    /// the same set.
    pub fn union(&mut self, k1: usize, k2: usize) -> bool {
        self.insert(k1);
        self.insert(k2);
        let root1 = self.strict_root_of(k1).expect("we just inserted k1");
        let root2 = self.strict_root_of(k2).expect("we just inserted k2");
        if root1 != root2 {
            self.parents[root2].set(root1);
            true
        } else {
            false
        }
    }

    pub fn new() -> UnionFind {
        Self { parents: vec![] }
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::UnionFind;

    #[test]
    fn aaa() {
        let mut union_find = UnionFind::new();
        union_find.union(0, 2);
        dbg!(union_find.root_of(0));
        dbg!(union_find.root_of(1));
        dbg!(union_find.root_of(2));
    }

    #[test]
    fn randoms() {
        let mut rng = rand::thread_rng();
        let mut union_find = UnionFind::new();
        for _ in 0..1000 {
            for i in 0..100 {
                dbg!(union_find.root_of(i));
            }
            let a = rng.gen_range(0..100);
            let b = rng.gen_range(0..100);
            union_find.union(a, b);
        }
    }
}
