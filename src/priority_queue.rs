//! A priority queue supporting random-access updates to the priority of elements
//!
//! Implemented with a binary heap

use crate::vec_map::*;
use std::cmp::Ordering;
use std::mem;

// would be a struct but I want to be able to convert it from a pair using
// `std::mem::transmute`
#[repr(transparent)]
#[derive(Debug, Copy, Clone)]
struct Entry<K, P> {
    pair: (K, P),
}

impl<K, P> Entry<K, P> {
    #[inline]
    fn new(k: K, p: P) -> Self {
        Self { pair: (k, p) }
    }

    #[inline]
    fn key(&self) -> K
    where
        K: Copy,
    {
        self.pair.0
    }

    #[inline]
    fn priority(&self) -> &P {
        &self.pair.1
    }
}

impl<K, P: PartialEq> PartialEq for Entry<K, P> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.priority() == other.priority()
    }
}
impl<K, P: Eq> Eq for Entry<K, P> {}

impl<K, P: PartialOrd> PartialOrd for Entry<K, P> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.priority().partial_cmp(other.priority())
    }
}
impl<K, P: Ord> Ord for Entry<K, P> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority().cmp(other.priority())
    }
}

#[derive(Debug, Clone)]
pub struct PriorityQueue<K: NumericId, P: Ord> {
    heap: Vec<Entry<K, P>>,
    // semantically: Map<K, index into heap>
    inds: VecMap<K, u32>,
    priorities: VecMap<K, P>,
}

#[inline]
fn parent(index: usize) -> usize {
    (index - 1) / 2
}
#[inline]
fn left(index: usize) -> usize {
    2 * index + 1
}
#[inline]
fn right(index: usize) -> usize {
    2 * index + 2
}

impl<K: NumericId, P: Ord + Copy> PriorityQueue<K, P> {
    /// The number of elements left in the heap
    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Make a new priority queue, with the given initial priorities, and the
    /// set of keys
    pub fn new(keys: &[K], priorities: VecMap<K, P>) -> Self {
        assert!(keys.len() < u32::MAX as usize);

        let mut inds = VecMap::new(vec![0; keys.len()]);
        for (i, &k) in keys.iter().enumerate() {
            inds[k] = i as u32;
        }

        let mut this = Self {
            heap: keys.iter().map(|&k| Entry::new(k, priorities[k])).collect(),
            inds,
            priorities,
        };

        // heapify
        for i in (0..parent(keys.len() - 1)).rev() {
            this.bubble_down(i);
        }

        this
    }

    /// Remove and return the key with the highest priority
    pub fn pop(&mut self) -> Option<K> {
        if self.is_empty() {
            None
        } else if self.len() == 1 {
            let key = self.heap.pop().unwrap().key();

            self.inds[key] = u32::MAX;

            Some(key)
        } else {
            let key = self.heap[0].key();
            self.inds[key] = u32::MAX;

            self.heap[0] = self.heap.pop().unwrap();
            self.bubble_down(0);

            Some(key)
        }
    }

    /// Remove the given key
    pub fn remove(&mut self, key: K) {
        let ind = mem::replace(&mut self.inds[key], u32::MAX);
        if ind >= self.len() as u32 - 1 {
            if ind == u32::MAX {
                return;
            } else if ind == self.len() as u32 - 1 {
                self.heap.pop().unwrap();
                return;
            } else {
                unreachable!();
            }
        }

        self.heap[ind as usize] = self.heap.pop().unwrap();
        self.bubble_down(ind as usize);
    }

    /// Add a key (that already used to be in the priority queue)
    pub fn re_add(&mut self, key: K) {
        debug_assert!(self.inds[key] == u32::MAX);
        self.heap.push(Entry::new(key, self.priorities[key]));
        self.bubble_up(self.len() - 1);
    }

    /// Apply a function to decrease the priority of a key
    pub fn decrease_priority(&mut self, key: K, f: impl FnOnce(&mut P)) {
        let _prev = self.priorities[key];
        f(&mut self.priorities[key]);
        let new = self.priorities[key];
        debug_assert!(new <= _prev);

        let i = self.inds[key] as usize;
        self.heap[i].pair.1 = new;
        self.bubble_down(i);
    }

    /// Apply a function to increase the priority of a key
    pub fn increase_priority(&mut self, key: K, f: impl FnOnce(&mut P)) {
        let _prev = self.priorities[key];
        f(&mut self.priorities[key]);
        let new = self.priorities[key];
        debug_assert!(new >= _prev);

        let i = self.inds[key] as usize;
        self.heap[i].pair.1 = new;
        self.bubble_up(i);
    }

    /// restore heap properties at index `i` by moving it down the heap
    fn bubble_down(&mut self, mut i: usize) {
        let len = self.len();

        while left(i) < len {
            if self.heap[i] < self.heap[left(i)] {
                if right(i) < len && self.heap[left(i)] < self.heap[right(i)] {
                    // swap with right; maintain indices; continue
                    self.heap.swap(i, right(i));
                    self.inds[self.heap[i].key()] = i as u32;
                    i = right(i);
                    continue;
                } else {
                    // swap with left; maintain indices; continue
                    self.heap.swap(i, left(i));
                    self.inds[self.heap[i].key()] = i as u32;
                    i = left(i);
                    continue;
                }
            } else {
                if right(i) < len && self.heap[i] < self.heap[right(i)] {
                    // swap with right; maintain indices; continue
                    self.heap.swap(i, right(i));
                    self.inds[self.heap[i].key()] = i as u32;
                    i = right(i);
                    continue;
                } else {
                    // i is the final index for this key
                    break;
                }
            }
        }

        self.inds[self.heap[i].key()] = i as u32;
    }

    /// restore heap properties at index `i` by moving it up the heap
    fn bubble_up(&mut self, mut i: usize) {
        while i > 0 {
            if self.heap[parent(i)] < self.heap[i] {
                // swap; maintain indices; continue
                self.heap.swap(parent(i), i);
                self.inds[self.heap[i].key()] = i as u32;
                i = parent(i);
                continue;
            } else {
                // i is the final index for this key
                break;
            }
        }

        self.inds[self.heap[i].key()] = i as u32;
    }
}
