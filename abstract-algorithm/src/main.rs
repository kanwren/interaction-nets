pub mod inet;
pub mod lambda;

fn main() {
    let term = {
        let args = std::env::args().collect::<Vec<_>>();
        if args.len() != 2 {
            panic!("Expected one argument");
        }
        args[1].clone()
    };
    match lambda::NamedTerm::parse(&term) {
        None => println!("failed to parse"),
        Some(x) => {
            println!("{}", x);
            match x.to_debruijn() {
                Err(e) => println!("no debruijn form: {}", e),
                Ok(x) => println!("{}", x),
            }
        }
    }
}
