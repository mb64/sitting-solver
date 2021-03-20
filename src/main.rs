pub mod cnf_reader;
pub mod data;
pub mod priority_queue;
pub mod simplify;
pub mod solver;
pub mod vec_map;

use std::{env, io};

fn main() -> io::Result<()> {
    let args: Vec<_> = env::args().collect();
    let (nvars, clauses) = cnf_reader::read_from_file(&args[1])?;

    println!(
        "Solving problem with {} vars and {} clauses",
        nvars,
        clauses.len()
    );
    let clauses = {
        let mut pre = simplify::Preprocessing::new(nvars, clauses);
        if pre.simplify().is_err() {
            println!("Preprocessing returned error");
            println!("{:#?}", pre);
            return Ok(());
        }
        pre.get_clauses()
    };
    println!("{} clauses left", clauses.len());
    let mut solver = solver::Solver::new(nvars, clauses);
    if solver.solve() {
        println!("Sat!");
        for (vid, &state) in solver.substitution.inner.iter().enumerate() {
            println!("{:4}: {:?}", vid + 1, state);
        }
        solver.verify();
    } else {
        println!("Unsat!");
    }

    Ok(())
}
