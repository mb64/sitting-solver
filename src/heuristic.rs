//! The heuristic for picking a literal to guess first
//!
//! Internally, it uses a priority queue supporting random-access updates to the
//! priority of elements, implemented with a binary heap

use crate::data::*;
use crate::vec_map::VecMap;
use std::cmp;
use std::mem;

#[derive(Debug, Copy, Clone)]
struct Entry {
    lit: Literal,
    priority: u32,
}

#[derive(Debug, Clone)]
pub struct Heuristic {
    heap: Vec<Entry>,
    inds: VecMap<VarId, u32>,
    priorities: VecMap<Literal, u32>,
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

impl Heuristic {
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
    pub fn new(vars: &[VarId], priorities: VecMap<Literal, u32>) -> Self {
        let nvars = priorities.inner.len() / 2;
        let mut inds = VecMap::new(vec![u32::MAX; nvars]);
        for (i, &k) in vars.iter().enumerate() {
            inds[k] = i as u32;
        }

        let mut this = Self {
            heap: vars
                .iter()
                .map(|&var| {
                    let mut lit = Literal::new(var);
                    if priorities[!lit] > priorities[lit] {
                        lit = !lit;
                    }
                    Entry {
                        lit,
                        priority: priorities[lit],
                    }
                })
                .collect(),
            inds,
            priorities,
        };

        // heapify
        if vars.len() >= 2 {
            for i in (0..=parent(vars.len() - 1)).rev() {
                this.bubble_down(i);
            }
        }

        this
    }

    /// Remove and return the literal with the highest priority
    pub fn pop(&mut self) -> Option<Literal> {
        if self.is_empty() {
            return None;
        }

        let lit = self.heap.swap_remove(0).lit;
        self.inds[lit.var_id()] = u32::MAX;

        if !self.is_empty() {
            self.bubble_down(0);
        }

        Some(lit)
    }

    /// Remove the given variable
    pub fn remove(&mut self, var: VarId) {
        let ind = mem::replace(&mut self.inds[var], u32::MAX);
        if ind == u32::MAX {
            return;
        }
        self.heap.swap_remove(ind as usize);

        if !self.is_empty() {
            self.bubble_down(ind as usize);
        }
    }

    /// Re-add a variable
    pub fn re_add(&mut self, var: VarId) {
        debug_assert!(self.inds[var] == u32::MAX);
        let mut lit = Literal::new(var);
        if self.priorities[!lit] > self.priorities[!lit] {
            lit = !lit;
        }
        self.heap.push(Entry {
            lit,
            priority: self.priorities[lit],
        });

        self.bubble_up(self.len() - 1);
    }

    /// Apply a function to decrease the priority of a literal
    pub fn decrease_priority(&mut self, lit: Literal, f: impl FnOnce(u32) -> u32) {
        let prev = self.priorities[lit];
        let new = f(prev);
        self.priorities[lit] = new;
        debug_assert!(new <= prev);

        if self.inds[lit.var_id()] != u32::MAX {
            let i = self.inds[lit.var_id()] as usize;
            self.heap[i].priority = cmp::max(new, self.priorities[!lit]);
            self.bubble_down(i);
        }
    }

    /// Apply a function to increase the priority of a literal
    pub fn increase_priority(&mut self, lit: Literal, f: impl FnOnce(u32) -> u32) {
        let prev = self.priorities[lit];
        let new = f(prev);
        self.priorities[lit] = new;
        debug_assert!(new >= prev);

        if self.inds[lit.var_id()] != u32::MAX {
            let i = self.inds[lit.var_id()] as usize;
            self.heap[i].priority = cmp::max(new, self.priorities[!lit]);
            self.bubble_up(i);
        }
    }

    /// restore heap properties at index `i` by moving it down the heap
    fn bubble_down(&mut self, mut i: usize) {
        let len = self.len();

        while left(i) < len {
            if self.heap[i].priority < self.heap[left(i)].priority {
                if right(i) < len && self.heap[left(i)].priority < self.heap[right(i)].priority {
                    // swap with right; maintain indices; continue
                    self.heap.swap(i, right(i));
                    self.inds[self.heap[i].lit.var_id()] = i as u32;
                    i = right(i);
                    continue;
                } else {
                    // swap with left; maintain indices; continue
                    self.heap.swap(i, left(i));
                    self.inds[self.heap[i].lit.var_id()] = i as u32;
                    i = left(i);
                    continue;
                }
            } else {
                if right(i) < len && self.heap[i].priority < self.heap[right(i)].priority {
                    // swap with right; maintain indices; continue
                    self.heap.swap(i, right(i));
                    self.inds[self.heap[i].lit.var_id()] = i as u32;
                    i = right(i);
                    continue;
                } else {
                    // i is the final index for this key
                    break;
                }
            }
        }

        self.inds[self.heap[i].lit.var_id()] = i as u32;
    }

    /// restore heap properties at index `i` by moving it up the heap
    fn bubble_up(&mut self, mut i: usize) {
        while i > 0 {
            if self.heap[parent(i)].priority < self.heap[i].priority {
                // swap; maintain indices; continue
                self.heap.swap(parent(i), i);
                self.inds[self.heap[i].lit.var_id()] = i as u32;
                i = parent(i);
                continue;
            } else {
                // i is the final index for this key
                break;
            }
        }

        self.inds[self.heap[i].lit.var_id()] = i as u32;
    }
}
