//! Read data from a file in the simplified DIMACS format used by the SAT competition
//!
//! See
//! (http://www.satcompetition.org/2011/format-benchmarks2011.html)[http://www.satcompetition.org/2011/format-benchmarks2011.html]
//! for a description of the format.
//!
//! This could be a lot faster, more robust and less hacky

use crate::data::{Clause, Literal, VarId};

use std::fs::File;
use std::io::{self, prelude::*, BufReader};
use tinyvec::TinyVec;

/// Returns (nvars, the clauses)
pub fn read_from_file(filename: &str) -> io::Result<(u32, Vec<Clause>)> {
    let file = File::open(filename)?;
    let reader = BufReader::new(file);

    let mut lines = reader.lines();

    let (nvars, ncls): (u32, u32) = loop {
        let line = lines.next().unwrap()?;

        if line.starts_with('c') {
            // comments
            continue;
        } else if line.starts_with('p') {
            // example line:
            // p cnf 5 3
            let parts: Vec<_> = line.split_whitespace().collect();
            break (parts[2].parse().unwrap(), parts[3].parse().unwrap());
        } else {
            panic!("Bad format: unexpected line \"{}\"", line);
        }
    };

    let mut clauses = Vec::with_capacity(ncls as usize);

    for line in lines {
        let line = line?;
        let mut clause = TinyVec::new();

        for chunk in line.split_whitespace() {
            let lit_id: i32 = chunk.parse().unwrap();
            // they're indexed by 1 in the format, and by 0 in this solver
            // negative means negated
            if lit_id < 0 {
                clause.push(!Literal::new(VarId::new((-lit_id - 1) as u32)));
            } else if lit_id > 0 {
                clause.push(Literal::new(VarId::new((lit_id - 1) as u32)));
            } else {
                // zero marks the end of the clause
                break;
            }
        }

        clauses.push(clause);
    }

    Ok((nvars, clauses))
}
