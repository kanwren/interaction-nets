use std::fmt::Display;

pub mod inet;
pub mod lambda;

fn disp<T: Display>(x: &T) -> String {
    const MAX_LEN: usize = 200;
    let s = format!("{}", x);
    if s.len() > MAX_LEN {
        s.chars().take(MAX_LEN).collect::<String>() + "..."
    } else {
        s
    }
}

fn usage() -> ! {
    eprintln!("Usage:");
    eprintln!("  abstract-algorithm EXPR");
    eprintln!("  abstract-algorithm -f FILE");
    std::process::exit(1);
}

fn main() {
    let term = {
        let args = std::env::args().collect::<Vec<_>>();
        let num_args = args.len();
        if num_args == 2 {
            args[1].clone()
        } else if num_args == 3 && args[1] == "-f" {
            let path = &args[2];
            let contents = std::fs::read(path).expect("failed to read file");
            String::from_utf8_lossy(&contents).to_string()
        } else {
            eprintln!("Invalid arguments");
            usage();
        }
    };
    match lambda::NamedTerm::parse(&term) {
        Err(e) => println!("{}", e),
        Ok(x) => {
            println!("named lambda:\n{}\n", disp(&x));
            match x.to_debruijn() {
                Err(e) => println!("no debruijn form: {}", e),
                Ok(x) => {
                    println!("debruijn form:\n{}\n", disp(&x));
                    let (reduced, stats) = inet::reduce_lambda_with_stats(&x);
                    println!("reduced form:\n{}\n", disp(&reduced));
                    println!("renamed:\n{}", disp(&reduced.to_named()));
                    if let Some(n) = reduced.to_nat() {
                        println!("\t(= {})", n);
                    }
                    println!();
                    println!(
                        "performed {} reductions ({} betas) in {:e} seconds",
                        stats.reductions,
                        stats.betas,
                        stats.time.as_secs_f64()
                    );
                }
            }
        }
    }
}
