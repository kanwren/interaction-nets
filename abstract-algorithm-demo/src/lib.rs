mod utils;

use std::fmt::Display;

use wasm_bindgen::prelude::*;
use abstract_algorithm::{lambda, inet};

fn disp<T: Display>(x: &T) -> String {
    const MAX_LEN: usize = 200;
    let s = format!("{}", x);
    if s.len() > MAX_LEN {
        s.chars().take(MAX_LEN).collect::<String>() + "..."
    } else {
        s
    }
}

#[wasm_bindgen]
pub struct ReductionResult {
    named_lambda: String,
    debruijn_lambda: String,
    reduced_debruijn_lambda: String,
    reduced_named_lambda: String,
    pub numeric_result: Option<usize>,
    pub reductions: usize,
    pub betas: usize,
}

#[wasm_bindgen]
impl ReductionResult {
    #[wasm_bindgen(getter)]
    pub fn named_lambda(&self) -> String { self.named_lambda.clone() }
    #[wasm_bindgen(getter)]
    pub fn debruijn_lambda(&self) -> String { self.debruijn_lambda.clone() }
    #[wasm_bindgen(getter)]
    pub fn reduced_debruijn_lambda(&self) -> String { self.reduced_debruijn_lambda.clone() }
    #[wasm_bindgen(getter)]
    pub fn reduced_named_lambda(&self) -> String { self.reduced_named_lambda.clone() }
}

#[wasm_bindgen]
pub fn do_reduction(input: &str) -> Result<ReductionResult, String> {
    match lambda::NamedTerm::parse(&input) {
        Err(e) => Err(format!("{}", e)),
        Ok(x) => {
            let named_lambda = disp(&x);
            match x.to_debruijn() {
                Err(e) => Err(format!("no debruijn form: {}", e)),
                Ok(x) => {
                    let debruijn_lambda = disp(&x);
                    let (reduced, stats) = inet::reduce_lambda_with_stats(&x);
                    let reduced_debruijn_lambda = disp(&reduced);
                    let reduced_named_lambda = disp(&reduced.to_named());
                    let numeric_result = reduced.to_nat();
                    let inet::Stats { reductions, betas } = stats;
                    let res = ReductionResult { named_lambda, debruijn_lambda, reduced_debruijn_lambda, reduced_named_lambda, numeric_result, reductions, betas };
                    Ok(res)
                }
            }
        }
    }
}

