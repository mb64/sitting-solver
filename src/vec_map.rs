use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// The trait that must be implemented by keys in an `VecMap`
pub trait NumericId: Copy {
    fn to_index(self) -> usize;
}

/// A dense map from (numeric id) keys to values
///
/// It's a convenience wrapper type around a `Vec<V>`
#[derive(Debug, Clone)]
pub struct VecMap<K: NumericId, V> {
    pub _marker: PhantomData<fn(K)>,
    pub inner: Vec<V>,
}

impl<K: NumericId, V> Index<K> for VecMap<K, V> {
    type Output = V;

    #[inline]
    fn index(&self, index: K) -> &Self::Output {
        &self.inner[index.to_index()]
    }
}

impl<K: NumericId, V> IndexMut<K> for VecMap<K, V> {
    #[inline]
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.inner[index.to_index()]
    }
}

impl<K: NumericId, V> VecMap<K, V> {
    pub fn new(inner: Vec<V>) -> Self {
        Self {
            _marker: PhantomData,
            inner,
        }
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }
}
