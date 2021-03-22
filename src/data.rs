//! Some helper datatypes

use crate::vec_map::NumericId;
use std::fmt::{self, Debug, Formatter};
use std::ops::Not;
use tinyvec::TinyVec;

/// The error raised when backtracking is needed, and/or the whole thing is
/// UNSAT
#[derive(Copy, Clone, Debug)]
pub struct Unsat;

/// A clause ID
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ClauseId(pub u32);

impl ClauseId {
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(id)
    }
}

impl NumericId for ClauseId {
    #[inline]
    fn to_index(self) -> usize {
        self.0 as usize
    }
}

/// A clause is the disjunction (OR) of a bunch of literals
// The number 6 chosen bc it's the most a TinyVec can store in 32 bytes
// (on x86_64, given that Literal is 4 bytes)
pub type Clause = TinyVec<[Literal; 6]>;

/// A variable ID
///
/// All variable ids are all less than 2^31
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct VarId(pub u32);

impl VarId {
    #[inline]
    pub fn new(id: u32) -> Self {
        assert!(id < 1 << 31);
        Self(id)
    }
}

impl NumericId for VarId {
    #[inline]
    fn to_index(self) -> usize {
        self.0 as usize
    }
}

/// A literal is either a variable or the negation of a variable
///
/// They are encoded in 32 bits using a 31-bit numerical id, plus a flag for
/// whether they're negated
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Literal {
    inner: u32,
}

impl Debug for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.is_negated() {
            write!(f, "Literal(neg {:?})", self.var_id())
        } else {
            write!(f, "Literal({:?})", self.var_id())
        }
    }
}

impl Not for Literal {
    type Output = Self;

    fn not(self) -> Self {
        Self {
            inner: self.inner ^ 1,
        }
    }
}

/// Required for `TinyVec`.  Please don't use.
impl Default for Literal {
    fn default() -> Self {
        Self { inner: 0 }
    }
}

impl Literal {
    /// Make a new (non-negated) literal with the given ID.
    #[inline]
    pub fn new(id: VarId) -> Self {
        Self { inner: id.0 << 1 }
    }

    #[inline]
    pub fn var_id(self) -> VarId {
        VarId(self.inner >> 1)
    }

    #[inline]
    pub fn is_negated(self) -> bool {
        self.inner & 1 != 0
    }
}

impl NumericId for Literal {
    #[inline]
    fn to_index(self) -> usize {
        self.inner as usize
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum VarState {
    False,
    True,
    /// Hasn't been assigned yet
    Unknown,
}
pub use VarState::*;

impl Not for VarState {
    type Output = VarState;

    fn not(self) -> Self::Output {
        match self {
            False => True,
            True => False,
            Unknown => Unknown,
        }
    }
}
