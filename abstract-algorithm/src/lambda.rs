use std::collections::HashMap;

use nom::bytes::complete::{is_not, tag};
use nom::character::complete::{alpha1, alphanumeric1, multispace1, one_of};
use nom::combinator::{cut, eof, map, opt, recognize, value};
use nom::multi::{many0, many0_count, many1};
use nom::sequence::{pair, preceded, terminated};
use nom::IResult;
use nom::{self, branch::alt, character::complete::char};

#[derive(Debug, PartialEq, Eq)]
pub enum NamedTerm {
    Var(String),
    Lam(String, Box<NamedTerm>),
    App(Box<NamedTerm>, Box<NamedTerm>),
}

fn decimal(i: &str) -> IResult<&str, usize> {
    map(recognize(many1(one_of("0123456789"))), |s: &str| {
        s.parse().expect("illegal number recognized")
    })(i)
}

fn identifier(i: &str) -> IResult<&str, String> {
    let h = alt((alpha1, tag("_")));
    let t = many0_count(alt((alphanumeric1, tag("_"))));
    map(recognize(pair(h, t)), &str::to_string)(i)
}

pub fn line_comment(i: &str) -> IResult<&str, ()> {
    value((), pair(tag("//"), opt(is_not("\n\r"))))(i)
}

fn ms0(i: &str) -> IResult<&str, ()> {
    value((), many0(alt((value((), multispace1), line_comment))))(i)
}

fn ms1(i: &str) -> IResult<&str, ()> {
    preceded(alt((value((), multispace1), line_comment)), ms0)(i)
}

impl NamedTerm {
    pub fn parse(input: &str) -> Result<Self, String> {
        fn parse_named_term(i: &str) -> IResult<&str, NamedTerm> {
            fn var(i: &str) -> IResult<&str, NamedTerm> {
                map(identifier, NamedTerm::Var)(i)
            }
            fn nat(i: &str) -> IResult<&str, NamedTerm> {
                map(preceded(opt(char('#')), decimal), NamedTerm::from_nat)(i)
            }
            fn lambda(i: &str) -> IResult<&str, NamedTerm> {
                let (i, _) = one_of("λ\\")(i)?;
                cut(|i| {
                    let (i, names) = many1(preceded(ms0, identifier))(i)?;
                    let (i, _) = preceded(ms0, char('.'))(i)?;
                    let (i, body) = preceded(ms0, named_term)(i)?;
                    let mut res = body;
                    for name in names.into_iter().rev() {
                        res = NamedTerm::Lam(name, Box::new(res));
                    }
                    Ok((i, res))
                })(i)
            }
            fn r#let(i: &str) -> IResult<&str, NamedTerm> {
                let (i, _) = terminated(tag("let"), ms1)(i)?;
                cut(|i| {
                    let (i, name) = identifier(i)?;
                    let (i, _) = preceded(ms0, char('='))(i)?;
                    let (i, value) = preceded(ms0, named_term)(i)?;
                    let (i, _) = preceded(ms0, char(';'))(i)?;
                    let (i, body) = preceded(ms0, named_term)(i)?;
                    let lam = NamedTerm::Lam(name, Box::new(body));
                    let term = NamedTerm::App(Box::new(lam), Box::new(value));
                    Ok((i, term))
                })(i)
            }
            fn parens(i: &str) -> IResult<&str, NamedTerm> {
                let (i, _) = char('(')(i)?;
                cut(terminated(preceded(ms0, named_term), pair(ms0, char(')'))))(i)
            }
            fn named_term(i: &str) -> IResult<&str, NamedTerm> {
                let (i, terms) = many1(preceded(ms0, alt((parens, lambda, r#let, nat, var))))(i)?;
                let mut term_iter = terms.into_iter();
                let mut acc = term_iter.next().expect("many1 produced no results");
                for arg in term_iter {
                    acc = NamedTerm::App(Box::new(acc), Box::new(arg));
                }
                Ok((i, acc))
            }
            terminated(named_term, pair(ms0, eof))(i)
        }
        parse_named_term(input)
            .map(|x| x.1)
            .map_err(|e| format!("{}", e))
    }

    pub fn to_debruijn(&self) -> Result<DebruijnTerm, String> {
        fn go(ctx: &HashMap<&str, usize>, term: &NamedTerm) -> Result<DebruijnTerm, String> {
            match term {
                NamedTerm::Var(x) => match ctx.get(&x.as_ref()).copied() {
                    Some(lvl) => Ok(DebruijnTerm::Var(lvl)),
                    None => Err(format!("free variable {} not found in scope", x)),
                },
                NamedTerm::App(x, y) => {
                    let xt = go(ctx, x)?;
                    let yt = go(ctx, y)?;
                    Ok(DebruijnTerm::App(Box::new(xt), Box::new(yt)))
                }
                NamedTerm::Lam(name, body) => {
                    let new_ctx = {
                        let mut inc_map = ctx
                            .iter()
                            .map(|(&x, &y)| (x, y + 1))
                            .collect::<HashMap<_, _>>();
                        inc_map.insert(name, 0);
                        inc_map
                    };
                    let body = go(&new_ctx, body)?;
                    Ok(DebruijnTerm::Lam(Box::new(body)))
                }
            }
        }
        go(&HashMap::new(), self)
    }

    pub fn from_nat(num: usize) -> Self {
        let mut term = NamedTerm::Var("z".into());
        for _ in 0..num {
            term = NamedTerm::App(Box::new(NamedTerm::Var("s".into())), Box::new(term));
        }
        term = NamedTerm::Lam(
            "s".into(),
            Box::new(NamedTerm::Lam("z".into(), Box::new(term))),
        );
        term
    }

    pub fn to_nat(&self) -> Option<usize> {
        self.to_debruijn().ok().and_then(|x| x.to_nat())
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
        Err(e) => panic!("{}", e),
        Ok(res) => assert_eq!(res, term),
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
        fn var(x: usize) -> DebruijnTerm {
            DebruijnTerm::Var(x)
        }
        fn lam(body: DebruijnTerm) -> DebruijnTerm {
            DebruijnTerm::Lam(Box::new(body))
        }
        fn app(x: DebruijnTerm, y: DebruijnTerm) -> DebruijnTerm {
            DebruijnTerm::App(Box::new(x), Box::new(y))
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
pub enum DebruijnTerm {
    Var(usize),
    Lam(Box<DebruijnTerm>),
    App(Box<DebruijnTerm>, Box<DebruijnTerm>),
}

impl DebruijnTerm {
    pub fn parse(input: &str) -> Result<Self, String> {
        fn parse_term(i: &str) -> IResult<&str, DebruijnTerm> {
            fn var(i: &str) -> IResult<&str, DebruijnTerm> {
                map(decimal, DebruijnTerm::Var)(i)
            }
            fn nat(i: &str) -> IResult<&str, DebruijnTerm> {
                let (i, _) = char('#')(i)?;
                cut(map(decimal, DebruijnTerm::from_nat))(i)
            }
            fn lambda(i: &str) -> IResult<&str, DebruijnTerm> {
                let (i, _) = one_of("λ\\")(i)?;
                cut(|i| {
                    let (i, body) = preceded(ms0, term)(i)?;
                    Ok((i, DebruijnTerm::Lam(Box::new(body))))
                })(i)
            }
            fn parens(i: &str) -> IResult<&str, DebruijnTerm> {
                let (i, _) = char('(')(i)?;
                cut(terminated(preceded(ms0, term), pair(ms0, char(')'))))(i)
            }
            fn term(i: &str) -> IResult<&str, DebruijnTerm> {
                let (i, terms) = many1(preceded(ms0, alt((parens, lambda, nat, var))))(i)?;
                let mut term_iter = terms.into_iter();
                let mut acc = term_iter.next().expect("many1 produced no results");
                for arg in term_iter {
                    acc = DebruijnTerm::App(Box::new(acc), Box::new(arg));
                }
                Ok((i, acc))
            }
            terminated(term, pair(ms0, eof))(i)
        }
        parse_term(input).map(|x| x.1).map_err(|e| format!("{}", e))
    }

    pub fn to_named(&self) -> NamedTerm {
        fn go(depth: usize, term: &DebruijnTerm) -> NamedTerm {
            match term {
                DebruijnTerm::Var(x) => NamedTerm::Var(format!("x{}", depth - x - 1)),
                DebruijnTerm::App(x, y) => {
                    NamedTerm::App(Box::new(go(depth, x)), Box::new(go(depth, y)))
                }
                DebruijnTerm::Lam(body) => {
                    NamedTerm::Lam(format!("x{}", depth), Box::new(go(depth + 1, body)))
                }
            }
        }
        go(0, self)
    }

    pub fn from_nat(num: usize) -> Self {
        // 0 = λf. λx. x
        // λf. λx. f (f (... f x)...)
        let mut term = DebruijnTerm::Var(0);
        for _ in 0..num {
            term = DebruijnTerm::App(Box::new(DebruijnTerm::Var(1)), Box::new(term));
        }
        term = DebruijnTerm::Lam(Box::new(DebruijnTerm::Lam(Box::new(term))));
        term
    }

    pub fn to_nat(&self) -> Option<usize> {
        match self {
            DebruijnTerm::Lam(body) => match &**body {
                DebruijnTerm::Lam(body) => {
                    let mut res = 0;
                    let mut body = &**body;
                    while let DebruijnTerm::App(a, b) = body {
                        if let DebruijnTerm::Var(1) = **a {
                            res += 1;
                            body = b;
                        } else {
                            return None;
                        }
                    }
                    if let DebruijnTerm::Var(0) = body {
                        Some(res)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }
}

#[test]
fn test_nat_to_church() {
    use DebruijnTerm::*;
    fn var(x: usize) -> DebruijnTerm {
        Var(x)
    }
    fn lam(body: DebruijnTerm) -> DebruijnTerm {
        Lam(Box::new(body))
    }
    fn app(x: DebruijnTerm, y: DebruijnTerm) -> DebruijnTerm {
        App(Box::new(x), Box::new(y))
    }
    let zero = lam(lam(var(0)));
    assert_eq!(DebruijnTerm::from_nat(0), zero);
    let three = lam(lam(app(var(1), app(var(1), app(var(1), var(0))))));
    assert_eq!(DebruijnTerm::from_nat(3), three);
}

#[test]
fn test_term_parser() {
    use DebruijnTerm::*;
    fn var(x: usize) -> DebruijnTerm {
        Var(x)
    }
    fn lam(body: DebruijnTerm) -> DebruijnTerm {
        Lam(Box::new(body))
    }
    fn app(x: DebruijnTerm, y: DebruijnTerm) -> DebruijnTerm {
        App(Box::new(x), Box::new(y))
    }
    let term = app(lam(lam(app(var(1), var(0)))), lam(lam(app(var(0), var(0)))));
    match DebruijnTerm::parse("(λλ1 0) (λ λ0 0)") {
        Err(e) => panic!("{}", e),
        Ok(res) => assert_eq!(res, term),
    }
}

#[test]
fn test_to_named() {
    let term = {
        fn var(x: usize) -> DebruijnTerm {
            DebruijnTerm::Var(x)
        }
        fn lam(body: DebruijnTerm) -> DebruijnTerm {
            DebruijnTerm::Lam(Box::new(body))
        }
        fn app(x: DebruijnTerm, y: DebruijnTerm) -> DebruijnTerm {
            DebruijnTerm::App(Box::new(x), Box::new(y))
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

impl std::fmt::Display for DebruijnTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_at(
            f: &mut std::fmt::Formatter<'_>,
            term: &DebruijnTerm,
            prec: usize,
        ) -> std::fmt::Result {
            match term {
                DebruijnTerm::Var(x) => write!(f, "{}", x)?,
                DebruijnTerm::Lam(body) => {
                    if prec > 0 {
                        write!(f, "(")?;
                    }
                    write!(f, "λ ")?;
                    fmt_at(f, body, 0)?;
                    if prec > 0 {
                        write!(f, ")")?;
                    }
                }
                DebruijnTerm::App(x, y) => {
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
        fn var(x: usize) -> DebruijnTerm {
            DebruijnTerm::Var(x)
        }
        fn lam(body: DebruijnTerm) -> DebruijnTerm {
            DebruijnTerm::Lam(Box::new(body))
        }
        fn app(x: DebruijnTerm, y: DebruijnTerm) -> DebruijnTerm {
            DebruijnTerm::App(Box::new(x), Box::new(y))
        }
        lam(lam(app(lam(var(0)), var(0))))
    };
    assert_eq!(format!("{}", term), "λ λ (λ 0) 0");
}
