mod cnf_reader;

use sitting_solver::Preprocessor;
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
        let mut pre = Preprocessor::new(nvars, clauses);
        if pre.simplify().is_err() {
            println!("Preprocessing returned error");
            println!("{:#?}", pre);
            return Ok(());
        }
        pre.finish()
    };
    if solver.solve().is_ok() {
        println!("Sat!");
        let model = post.postprocess(&solver);
        for (vid, &state) in model.inner.iter().enumerate() {
            println!("{:4}: {:?}", vid + 1, state);
        }
    } else {
        println!("Unsat!");
    }

    Ok(())
}
