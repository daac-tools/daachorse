use alloc::vec::Vec;

#[derive(Clone, Default)]
pub(crate) enum EdgeMap<L> {
    #[default]
    Empty,
    One((L, u32)),
    Many(Vec<(L, u32)>),
}

impl<L> EdgeMap<L>
where
    L: Ord + Copy,
{
    pub(crate) fn insert(&mut self, key: L, value: u32) {
        match self {
            Self::Empty => {
                *self = Self::One((key, value));
            }
            Self::One((k, v)) => {
                if key == *k {
                    *v = value;
                    return;
                }
                let mut entries = Vec::with_capacity(2);
                if key < *k {
                    entries.push((key, value));
                    entries.push((*k, *v));
                } else {
                    entries.push((*k, *v));
                    entries.push((key, value));
                }
                *self = Self::Many(entries);
            }
            Self::Many(entries) => match entries.binary_search_by_key(&key, |(k, _)| *k) {
                Ok(pos) => {
                    entries[pos].1 = value;
                }
                Err(pos) => {
                    entries.insert(pos, (key, value));
                }
            },
        }
    }

    pub(crate) fn get(&self, key: &L) -> Option<&u32> {
        match self {
            Self::Empty => None,
            Self::One((k, v)) => (*key == *k).then_some(v),
            Self::Many(entries) => entries
                .binary_search_by_key(key, |(k, _)| *k)
                .ok()
                .map(|pos| &entries[pos].1),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub(crate) fn keys(&self) -> impl Iterator<Item = &L> {
        self.iter().map(|(k, _)| k)
    }

    pub(crate) fn values(&self) -> impl Iterator<Item = &u32> {
        self.iter().map(|(_, v)| v)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &(L, u32)> {
        match self {
            Self::Empty => [].iter(),
            Self::One(entry) => core::slice::from_ref(entry).iter(),
            Self::Many(entries) => entries.iter(),
        }
    }
}
