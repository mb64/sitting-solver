//! Heuristics for which literal to guess, and which clause to get rid of first
//!
//! They both use a priority queue supporting random-access updates to the
//! priority of elements, implemented with a binary heap

use crate::data::*;
use crate::vec_map::VecMap;
use std::cmp;
use std::mem;

trait Indexer<K> {
    fn index_of(&self, key: K) -> usize;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct VarIndexer;
impl Indexer<Literal> for VarIndexer {
    #[inline]
    fn index_of(&self, key: Literal) -> usize {
        key.var_id().0 as usize
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct LearnedClauseIndexer(u32);
impl Indexer<ClauseId> for LearnedClauseIndexer {
    #[inline]
    fn index_of(&self, key: ClauseId) -> usize {
        (key.0 - self.0) as usize
    }
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Entry<K> {
    key: K,
    priority: u32,
}

/// The shared heap implementation for both heuristics
#[derive(Debug, Clone, Eq, PartialEq)]
struct PriorityQueue<K, I: Indexer<K>> {
    heap: Vec<Entry<K>>,
    inds: Vec<u32>,
    indexer: I,
}

impl<K: Copy, I: Indexer<K>> PriorityQueue<K, I> {
    #[inline]
    fn len(&self) -> usize {
        self.heap.len()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Remove and return the key with the highest priority
    fn pop(&mut self) -> Option<K> {
        if self.is_empty() {
            return None;
        }

        let key = self.heap.swap_remove(0).key;
        self.inds[self.indexer.index_of(key)] = u32::MAX;

        if !self.is_empty() {
            self.bubble_down(0);
        }

        Some(key)
    }

    /// restore heap properties at index `i` by moving it down the heap
    fn bubble_down(&mut self, mut i: usize) {
        let len = self.len();

        while left(i) < len {
            if self.heap[i].priority < self.heap[left(i)].priority {
                if right(i) < len && self.heap[left(i)].priority < self.heap[right(i)].priority {
                    // swap with right; maintain indices; continue
                    self.heap.swap(i, right(i));
                    self.inds[self.indexer.index_of(self.heap[i].key)] = i as u32;
                    i = right(i);
                    continue;
                } else {
                    // swap with left; maintain indices; continue
                    self.heap.swap(i, left(i));
                    self.inds[self.indexer.index_of(self.heap[i].key)] = i as u32;
                    i = left(i);
                    continue;
                }
            } else {
                if right(i) < len && self.heap[i].priority < self.heap[right(i)].priority {
                    // swap with right; maintain indices; continue
                    self.heap.swap(i, right(i));
                    self.inds[self.indexer.index_of(self.heap[i].key)] = i as u32;
                    i = right(i);
                    continue;
                } else {
                    // i is the final index for this key
                    break;
                }
            }
        }

        self.inds[self.indexer.index_of(self.heap[i].key)] = i as u32;
    }

    /// restore heap properties at index `i` by moving it up the heap
    fn bubble_up(&mut self, mut i: usize) {
        while i > 0 {
            if self.heap[parent(i)].priority < self.heap[i].priority {
                // swap; maintain indices; continue
                self.heap.swap(parent(i), i);
                self.inds[self.indexer.index_of(self.heap[i].key)] = i as u32;
                i = parent(i);
                continue;
            } else {
                // i is the final index for this key
                break;
            }
        }

        self.inds[self.indexer.index_of(self.heap[i].key)] = i as u32;
    }
}

/// The heuristic for picking a literal to guess first
#[derive(Debug, Clone)]
pub struct LitHeuristic {
    pq: PriorityQueue<Literal, VarIndexer>,
    priorities: VecMap<Literal, u32>,
}

impl LitHeuristic {
    /// The number of elements left in the heap
    #[inline]
    pub fn len(&self) -> usize {
        self.pq.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.pq.is_empty()
    }

    /// Make a new heuristic, with the given initial priorities, and the set of
    /// keys
    pub fn new(vars: &[VarId], priorities: VecMap<Literal, u32>) -> Self {
        let nvars = priorities.inner.len() / 2;
        let mut inds = VecMap::new(vec![u32::MAX; nvars]);
        for (i, &k) in vars.iter().enumerate() {
            inds[k] = i as u32;
        }

        let mut this = Self {
            pq: PriorityQueue {
                heap: vars
                    .iter()
                    .map(|&var| {
                        let mut lit = Literal::new(var);
                        if priorities[!lit] > priorities[lit] {
                            lit = !lit;
                        }
                        Entry {
                            key: lit,
                            priority: priorities[lit],
                        }
                    })
                    .collect(),
                inds: inds.inner,
                indexer: VarIndexer,
            },
            priorities,
        };

        // heapify
        if vars.len() >= 2 {
            for i in (0..=parent(vars.len() - 1)).rev() {
                this.pq.bubble_down(i);
            }
        }

        this
    }

    /// Remove and return the literal with the highest priority
    pub fn pop(&mut self) -> Option<Literal> {
        self.pq.pop()
    }

    /// Remove the given variable
    pub fn remove(&mut self, var: VarId) {
        let ind = mem::replace(&mut self.pq.inds[var.0 as usize], u32::MAX);
        if ind == u32::MAX {
            return;
        }
        self.pq.heap.swap_remove(ind as usize);

        if (ind as usize) < self.len() {
            self.pq.bubble_down(ind as usize);
        }
    }

    /// Re-add a variable
    pub fn re_add(&mut self, var: VarId) {
        debug_assert!(self.pq.inds[var.0 as usize] == u32::MAX);
        let mut lit = Literal::new(var);
        if self.priorities[!lit] > self.priorities[!lit] {
            lit = !lit;
        }
        self.pq.heap.push(Entry {
            key: lit,
            priority: self.priorities[lit],
        });

        self.pq.bubble_up(self.len() - 1);
    }

    /// Apply a function to decrease the priority of a literal
    pub fn decrease_priority(&mut self, lit: Literal, f: impl FnOnce(u32) -> u32) {
        let prev = self.priorities[lit];
        let new = f(prev);
        self.priorities[lit] = new;
        debug_assert!(new <= prev);

        if self.pq.inds[lit.var_id().0 as usize] != u32::MAX {
            let i = self.pq.inds[lit.var_id().0 as usize] as usize;
            self.pq.heap[i].priority = cmp::max(new, self.priorities[!lit]);
            self.pq.bubble_down(i);
        }
    }

    /// Apply a function to increase the priority of a literal
    pub fn increase_priority(&mut self, lit: Literal, f: impl FnOnce(u32) -> u32) {
        let prev = self.priorities[lit];
        let new = f(prev);
        self.priorities[lit] = new;
        debug_assert!(new >= prev);

        if self.pq.inds[lit.var_id().0 as usize] != u32::MAX {
            let i = self.pq.inds[lit.var_id().0 as usize] as usize;
            self.pq.heap[i].priority = cmp::max(new, self.priorities[!lit]);
            self.pq.bubble_up(i);
        }
    }
}

/// The heuristic for which clauses to keep.
///
/// Currently, a simple LRU scheme.
#[derive(Debug, Clone)]
pub struct ClauseHeuristic {
    pq: PriorityQueue<ClauseId, LearnedClauseIndexer>,
    /// Priority = u32::MAX - generation
    /// (so older generation clauses have a higher priority for removal)
    priorities: Vec<u32>,
    /// The current generation.
    gen: u32,
}

impl ClauseHeuristic {
    pub fn new(nclauses: usize, learning_cap: usize) -> Self {
        Self {
            pq: PriorityQueue {
                heap: Vec::with_capacity(learning_cap),
                inds: Vec::with_capacity(learning_cap),
                indexer: LearnedClauseIndexer(nclauses as u32),
            },
            priorities: Vec::with_capacity(learning_cap),
            gen: 0,
        }
    }

    pub fn num_orig_clauses(&self) -> u32 {
        self.pq.indexer.0
    }

    pub fn is_learned(&self, cid: ClauseId) -> bool {
        cid.0 >= self.num_orig_clauses()
    }

    /// The current maximum number of learned clauses
    pub fn learning_cap(&self) -> usize {
        debug_assert_eq!(self.priorities.capacity(), self.pq.heap.capacity());
        debug_assert_eq!(self.priorities.capacity(), self.pq.inds.capacity());
        self.priorities.capacity()
    }

    /// Temporarily remove this clause from consideration for removal, since
    /// it's a reason clause
    pub fn dont_remove(&mut self, cid: ClauseId) {
        if !self.is_learned(cid) {
            return;
        }
        // println!("Promising not to remove {:?}", cid);
        let ind = mem::replace(&mut self.pq.inds[self.pq.indexer.index_of(cid)], u32::MAX);
        self.pq.heap.swap_remove(ind as usize);
        if (ind as usize) < self.pq.len() {
            self.pq.bubble_down(ind as usize);
        }
    }

    /// When backtracking a variable assignment, so a clause is no longer a
    /// reason clause
    pub fn ok_to_remove_now(&mut self, cid: ClauseId) {
        if !self.is_learned(cid) {
            return;
        }
        // println!("Ok to remove {:?}", cid);

        // Update the priority
        self.priorities[self.pq.indexer.index_of(cid)] = u32::MAX - self.gen;

        let ind = self.pq.len();
        self.pq.heap.push(Entry {
            key: cid,
            priority: self.priorities[self.pq.indexer.index_of(cid)],
        });
        self.pq.bubble_up(ind);
    }

    /// If it returns `Some(cid)`, replace that clause with the learned clause
    ///
    /// If it returns `None`, add the learned clause to the end
    ///
    /// The resulting clause is by default up for removal unless you call
    /// [`ClauseHeuristic::dont_remove`] for it
    pub fn where_to_put_new_clause(&mut self) -> Option<ClauseId> {
        // Update priority
        self.gen += 2;
        let priority = u32::MAX - self.gen - 1;

        let cid;
        let result;
        if self.priorities.len() == self.learning_cap() {
            cid = self.pq.pop().unwrap();
            result = Some(cid);
            self.priorities[self.pq.indexer.index_of(cid)] = priority;
        } else {
            cid = ClauseId(self.num_orig_clauses() + self.priorities.len() as u32);
            result = None;
            self.priorities.push(priority);
            self.pq.inds.push(u32::MAX);
        }

        let ind = self.pq.len();
        self.pq.heap.push(Entry { key: cid, priority });
        self.pq.bubble_up(ind);

        result
    }
}
