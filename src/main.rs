pub mod cnf_reader;
pub mod core;
pub mod data;
pub mod heuristic;
pub mod simplify;
pub mod vec_map;

use std::{env, io};

fn main() -> io::Result<()> {
    pretty_env_logger::init();

    let args: Vec<_> = env::args().collect();
    let (nvars, clauses) = cnf_reader::read_from_file(&args[1])?;

    println!(
        "Solving problem with {} vars and {} clauses",
        nvars,
        clauses.len()
    );
    let (mut solver, post) = {
        let mut pre = simplify::Preprocessing::new(nvars, clauses);
        if pre.simplify().is_err() {
            println!("Preprocessing returned error");
            println!("{:#?}", pre);
            return Ok(());
        }
        pre.finish()
    };
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
