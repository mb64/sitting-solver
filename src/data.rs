//! Some helper datatypes

use crate::vec_map::NumericId;
use std::fmt::{self, Debug, Formatter};
use std::ops::Not;

/// A clause ID
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ClauseId(u32);

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
// Memory TODO: maybe arena-allocate (will be more helpful with
// conflict-driven clause learning, since then we'll need to allocate new
// clauses)
pub type Clause = Box<[Literal]>;

/// A variable ID
///
/// All variable ids are all less than 2^31
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct VarId(u32);

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
/// They are encoded in 32 bits using a 31-bit numerical id, plus a flag for whether they're
/// negated
#[derive(Copy, Clone, Eq, PartialEq)]
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

///// A clause is a set of literals; it represents their disjunction (OR)
/////
///// A clause is only updated when one of its watched literals changes
//#[derive(Debug, Eq, PartialEq, Clone)]
//pub struct Clause {
//    /// An unordered vector of literals
//    /// Note: only indices `0..len` are active literals
//    // Memory TODO: possibly arena-allocate it (`&'arena mut [Literal]`)
//    pub literals: Box<[Literal]>,
//    pub len: usize,
//}

//impl Clause {
//    pub fn new(literals: Vec<Literal>) -> Self {
//        Self {
//            len: literals.len(),
//            literals: literals.into(),
//        }
//    }

//    /// A clause becomes inactive when all its conditions are satisfied
//    pub fn is_active(&self) -> bool {
//        self.len >= 2
//    }

//    /// The two watched literals for this clause (they're the ones at the front)
//    pub fn watched_literals(&self) -> (Literal, Literal) {
//        assert!(self.is_active());
//        (self.literals[0], self.literals[1])
//    }
//}

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

///// A single entry in the trail; it says how to backtrack one thing
//#[derive(Debug, Copy, Clone, Eq, PartialEq)]
//pub enum Breadcrumb {
//    /// A clause was visited and its length was shortened (maybe to 0, if it was
//    /// solved)
//    ///
//    /// To backtrack: set the length to `prev_len` and increment the
//    /// `clause_count` of the variables involved.
//    /// If the length was previously 0, then its watched_vars need updating
//    Clause { id: ClauseId, prev_len: u32 },

//    /// The only possible value for a variable was determined.
//    ///
//    /// To backtrack: TODO
//    SolveVar(VarId),

//    /// The value of a variable was nondeterministically chosen.
//    ///
//    /// To backtrack: TODO
//    /// Then add `SolveVar(varid)` to the trail and try the other
//    /// option.
//    GuessVar(VarId),
//}
