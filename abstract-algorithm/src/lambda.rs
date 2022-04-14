use std::collections::HashMap;

use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, alphanumeric1, multispace0, one_of};
use nom::combinator::{eof, map, recognize};
use nom::multi::{many0_count, many1};
use nom::sequence::{delimited, pair, preceded, terminated};
use nom::IResult;
use nom::{self, branch::alt, character::complete::char};

#[derive(Debug, PartialEq, Eq)]
pub enum NamedTerm {
    Var(String),
    Lam(String, Box<NamedTerm>),
    App(Box<NamedTerm>, Box<NamedTerm>),
}

impl NamedTerm {
    pub fn parse(input: &str) -> Option<Self> {
        fn parse_named_term(i: &str) -> IResult<&str, NamedTerm> {
            fn identifier(i: &str) -> IResult<&str, String> {
                let h = alt((alpha1, tag("_")));
                let t = many0_count(alt((alphanumeric1, tag("_"))));
                map(recognize(pair(h, t)), &str::to_string)(i)
            }
            fn var(i: &str) -> IResult<&str, NamedTerm> {
                map(identifier, NamedTerm::Var)(i)
            }
            fn lambda(i: &str) -> IResult<&str, NamedTerm> {
                let (i, _) = one_of("λ\\")(i)?;
                let (i, names) = many1(preceded(multispace0, identifier))(i)?;
                let (i, _) = preceded(multispace0, char('.'))(i)?;
                let (i, body) = preceded(multispace0, named_term)(i)?;
                let mut res = body;
                for name in names.into_iter().rev() {
                    res = NamedTerm::Lam(name, Box::new(res));
                }
                Ok((i, res))
            }
            fn parens(i: &str) -> IResult<&str, NamedTerm> {
                delimited(
                    pair(char('('), multispace0),
                    named_term,
                    pair(multispace0, char(')')),
                )(i)
            }
            fn named_term(i: &str) -> IResult<&str, NamedTerm> {
                let (i, terms) = many1(preceded(multispace0, alt((parens, lambda, var))))(i)?;
                let mut term_iter = terms.into_iter();
                let mut acc = term_iter.next().expect("many1 produced no results");
                for arg in term_iter {
                    acc = NamedTerm::App(Box::new(acc), Box::new(arg));
                }
                Ok((i, acc))
            }
            terminated(named_term, pair(multispace0, eof))(i)
        }
        parse_named_term(input).ok().map(|x| x.1)
    }

    pub fn to_debruijn(self) -> Result<Term, String> {
        fn go(ctx: &HashMap<String, usize>, term: NamedTerm) -> Result<Term, String> {
            match term {
                NamedTerm::Var(x) => match ctx.get(&x).copied() {
                    Some(lvl) => Ok(Term::Var(lvl)),
                    None => Err(format!("free variable {} not found in scope", x)),
                },
                NamedTerm::App(x, y) => {
                    let xt = go(ctx, *x)?;
                    let yt = go(ctx, *y)?;
                    Ok(Term::App(Box::new(xt), Box::new(yt)))
                }
                NamedTerm::Lam(name, body) => {
                    let new_ctx = {
                        let mut inc_map = ctx
                            .iter()
                            .map(|(x, &y)| (x.clone(), y + 1))
                            .collect::<HashMap<_, _>>();
                        inc_map.insert(name, 0);
                        inc_map
                    };
                    let body = go(&new_ctx, *body)?;
                    Ok(Term::Lam(Box::new(body)))
                }
            }
        }
        go(&HashMap::new(), self)
    }
}

#[test]
fn test_named_term_parser() {
    use NamedTerm::*;
    fn var(x: impl Into<String>) -> NamedTerm {
        Var(x.into())
    }
    fn lam(name: impl Into<String>, body: NamedTerm) -> NamedTerm {
        Lam(name.into(), Box::new(body))
    }
    fn app(x: NamedTerm, y: NamedTerm) -> NamedTerm {
        App(Box::new(x), Box::new(y))
    }
    let term = app(
        lam("x", lam("y", app(var("x"), var("y")))),
        app(app(var("f"), var("x")), var("y")),
    );
    match NamedTerm::parse("(λx. λ y . x y) (f x y)") {
        None => panic!("failed to parse"),
        Some(res) => assert_eq!(res, term),
    }
}

#[test]
fn test_to_debruijn() {
    let term = {
        fn var(x: impl Into<String>) -> NamedTerm {
            NamedTerm::Var(x.into())
        }
        fn lam(name: impl Into<String>, body: NamedTerm) -> NamedTerm {
            NamedTerm::Lam(name.into(), Box::new(body))
        }
        fn app(x: NamedTerm, y: NamedTerm) -> NamedTerm {
            NamedTerm::App(Box::new(x), Box::new(y))
        }
        lam("x", lam("y", app(lam("x", var("x")), var("y"))))
    };
    let term2 = {
        fn var(x: usize) -> Term {
            Term::Var(x)
        }
        fn lam(body: Term) -> Term {
            Term::Lam(Box::new(body))
        }
        fn app(x: Term, y: Term) -> Term {
            Term::App(Box::new(x), Box::new(y))
        }
        lam(lam(app(lam(var(0)), var(0))))
    };
    match term.to_debruijn() {
        Ok(t) => assert_eq!(t, term2),
        Err(e) => panic!("failed to convert to debruijn indices: {}", e),
    }
}

impl std::fmt::Display for NamedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_at(
            f: &mut std::fmt::Formatter<'_>,
            term: &NamedTerm,
            prec: usize,
        ) -> std::fmt::Result {
            match term {
                NamedTerm::Var(x) => write!(f, "{}", x)?,
                NamedTerm::Lam(name, body) => {
                    if prec > 0 {
                        write!(f, "(")?;
                    }
                    write!(f, "λ{}", name)?;
                    let mut body = &**body;
                    while let NamedTerm::Lam(name, new_body) = body {
                        write!(f, " {}", name)?;
                        body = new_body;
                    }
                    write!(f, ". ")?;
                    fmt_at(f, body, 0)?;
                    if prec > 0 {
                        write!(f, ")")?;
                    }
                }
                NamedTerm::App(x, y) => {
                    if prec > 1 {
                        write!(f, "(")?;
                    }
                    fmt_at(f, x, 1)?;
                    write!(f, " ")?;
                    fmt_at(f, y, 2)?;
                    if prec > 1 {
                        write!(f, ")")?;
                    }
                }
            }
            Ok(())
        }
        fmt_at(f, self, 0)
    }
}

#[test]
fn test_named_term_display() {
    use NamedTerm::*;
    fn var(x: impl Into<String>) -> NamedTerm {
        Var(x.into())
    }
    fn lam(name: impl Into<String>, body: NamedTerm) -> NamedTerm {
        Lam(name.into(), Box::new(body))
    }
    fn app(x: NamedTerm, y: NamedTerm) -> NamedTerm {
        App(Box::new(x), Box::new(y))
    }
    let term = lam("x", lam("y", app(app(var("f"), var("x")), var("y"))));
    assert_eq!(format!("{}", term), "λx. λy. f x y");
    let term = lam("x", lam("y", app(var("f"), app(var("x"), var("y")))));
    assert_eq!(format!("{}", term), "λx. λy. f (x y)");
    let term = app(
        lam("x", lam("y", app(var("x"), var("y")))),
        app(app(var("f"), var("x")), var("y")),
    );
    assert_eq!(format!("{}", term), "(λx. λy. x y) (f x y)");
}

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    Var(usize),
    Lam(Box<Term>),
    App(Box<Term>, Box<Term>),
}

impl Term {
    pub fn nat_to_church(num: usize) -> Self {
        // 0 = λf. λx. x
        // λf. λx. f (f (... f x)...)
        let mut term = Term::Var(0);
        for _ in 0..num {
            term = Term::App(Box::new(Term::Var(1)), Box::new(term));
        }
        term = Term::Lam(Box::new(Term::Lam(Box::new(term))));
        term
    }

    pub fn parse(input: &str) -> Option<Self> {
        fn parse_term(i: &str) -> IResult<&str, Term> {
            fn var(i: &str) -> IResult<&str, Term> {
                map(recognize(many1(one_of("0123456789"))), |s: &str| {
                    Term::Var(s.parse().expect("illegal number recognized"))
                })(i)
            }
            fn lambda(i: &str) -> IResult<&str, Term> {
                let (i, _) = one_of("λ\\")(i)?;
                let (i, body) = preceded(multispace0, term)(i)?;
                Ok((i, Term::Lam(Box::new(body))))
            }
            fn parens(i: &str) -> IResult<&str, Term> {
                delimited(
                    pair(char('('), multispace0),
                    term,
                    pair(multispace0, char(')')),
                )(i)
            }
            fn term(i: &str) -> IResult<&str, Term> {
                let (i, terms) = many1(preceded(multispace0, alt((parens, lambda, var))))(i)?;
                let mut term_iter = terms.into_iter();
                let mut acc = term_iter.next().expect("many1 produced no results");
                for arg in term_iter {
                    acc = Term::App(Box::new(acc), Box::new(arg));
                }
                Ok((i, acc))
            }
            terminated(term, pair(multispace0, eof))(i)
        }
        parse_term(input).ok().map(|x| x.1)
    }

    pub fn to_named(self) -> NamedTerm {
        fn go(depth: usize, term: Term) -> NamedTerm {
            match term {
                Term::Var(x) => NamedTerm::Var(format!("x{}", depth - x - 1)),
                Term::App(x, y) => NamedTerm::App(Box::new(go(depth, *x)), Box::new(go(depth, *y))),
                Term::Lam(body) => {
                    NamedTerm::Lam(format!("x{}", depth), Box::new(go(depth + 1, *body)))
                }
            }
        }
        go(0, self)
    }
}

#[test]
fn test_nat_to_church() {
    use Term::*;
    fn var(x: usize) -> Term {
        Var(x)
    }
    fn lam(body: Term) -> Term {
        Lam(Box::new(body))
    }
    fn app(x: Term, y: Term) -> Term {
        App(Box::new(x), Box::new(y))
    }
    let zero = lam(lam(var(0)));
    assert_eq!(Term::nat_to_church(0), zero);
    let three = lam(lam(app(var(1), app(var(1), app(var(1), var(0))))));
    assert_eq!(Term::nat_to_church(3), three);
}

#[test]
fn test_term_parser() {
    use Term::*;
    fn var(x: usize) -> Term {
        Var(x)
    }
    fn lam(body: Term) -> Term {
        Lam(Box::new(body))
    }
    fn app(x: Term, y: Term) -> Term {
        App(Box::new(x), Box::new(y))
    }
    let term = app(lam(lam(app(var(1), var(0)))), lam(lam(app(var(0), var(0)))));
    match Term::parse("(λλ1 0) (λ λ0 0)") {
        None => panic!("failed to parse"),
        Some(res) => assert_eq!(res, term),
    }
}

#[test]
fn test_to_named() {
    let term = {
        fn var(x: usize) -> Term {
            Term::Var(x)
        }
        fn lam(body: Term) -> Term {
            Term::Lam(Box::new(body))
        }
        fn app(x: Term, y: Term) -> Term {
            Term::App(Box::new(x), Box::new(y))
        }
        lam(lam(app(lam(var(0)), var(0))))
    };
    let term2 = {
        fn var(x: impl Into<String>) -> NamedTerm {
            NamedTerm::Var(x.into())
        }
        fn lam(name: impl Into<String>, body: NamedTerm) -> NamedTerm {
            NamedTerm::Lam(name.into(), Box::new(body))
        }
        fn app(x: NamedTerm, y: NamedTerm) -> NamedTerm {
            NamedTerm::App(Box::new(x), Box::new(y))
        }
        lam("x0", lam("x1", app(lam("x2", var("x2")), var("x1"))))
    };
    assert_eq!(term.to_named(), term2);
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_at(f: &mut std::fmt::Formatter<'_>, term: &Term, prec: usize) -> std::fmt::Result {
            match term {
                Term::Var(x) => write!(f, "{}", x)?,
                Term::Lam(body) => {
                    if prec > 0 {
                        write!(f, "(")?;
                    }
                    write!(f, "λ ")?;
                    fmt_at(f, body, 0)?;
                    if prec > 0 {
                        write!(f, ")")?;
                    }
                }
                Term::App(x, y) => {
                    if prec > 1 {
                        write!(f, "(")?;
                    }
                    fmt_at(f, x, 1)?;
                    write!(f, " ")?;
                    fmt_at(f, y, 2)?;
                    if prec > 1 {
                        write!(f, ")")?;
                    }
                }
            }
            Ok(())
        }
        fmt_at(f, self, 0)
    }
}

#[test]
fn test_debruijn_display() {
    let term = {
        fn var(x: usize) -> Term {
            Term::Var(x)
        }
        fn lam(body: Term) -> Term {
            Term::Lam(Box::new(body))
        }
        fn app(x: Term, y: Term) -> Term {
            Term::App(Box::new(x), Box::new(y))
        }
        lam(lam(app(lam(var(0)), var(0))))
    };
    assert_eq!(format!("{}", term), "λ λ (λ 0) 0");
}
