// Copyright 2023 Redglyph
//
// Unit tests.

#![cfg(test)]

use std::str::FromStr;
use crate::*;

use proc_macro2::{Span, TokenStream};

fn annotate_error(text: &str, msg: &str, span: Span) -> String {
    // only works for single-lined sources:
    assert!(!text.contains('\n'));
    let mut msg = msg.to_string();
    msg.push('\n');
    msg.push_str(text);
    msg.push('\n');
    let start = span.start().column;
    let end = span.end().column;
    if start > 0 || end > 0 {
        msg.push_str(&" ".repeat(start));
    } else {
        msg.push_str(&" ".repeat(text.len()));
    }
    msg.push_str(&"^".repeat(end - start + 1));
    msg
}

fn try_parse<T: Parse>(args: TokenStream, text: &str) -> Result<T, String> {
    match parse2::<T>(args.clone()) {
        Ok(subst) => Ok(subst),
        Err(err) => {
            let msg = annotate_error(text, &err.to_string(), err.span());
            // println!("{msg}");
            Err(msg)
        }
    }
}

fn try_get_tokenstream(string: &str) -> Result<TokenStream, String> {
    match TokenStream::from_str(string) {
        Ok(s) => Ok(s),
        Err(err) => {
            Err(format!("could not transform test string into TokenStream: {}",
                        annotate_error(string, &err.to_string(), err.span())))
        }
    }
}

/// `tokenstream!(text: &str, error: mut int)`
///
/// Transforms the string slice `text` into a TokenStream. In case of error,
/// displays the location of the problem, increments the `error` variable,
/// and `continue` to the next loop iteration.
///
/// Must be used within a loop.
macro_rules! tokenstream {
    ($s:expr, $e:ident) => {
        match try_get_tokenstream($s) {
            Ok(s) => s,
            Err(err) => {
                println!("{}", err);
                $e += 1;
                continue
            }
        }
    }
}

/// `parse_str!(T: Parse, text: &str, error: mut int)`
///
/// Parses the string slice `text` as type `T`, which must implement the `Parse` trait.
/// In case of error, displays the location of the problem, increments the `error` variable
/// and `continue` to the next loop iteration.
///
/// Must be used within a loop.
macro_rules! parse_str {
    ($t:ty, $s:expr, $e:ident) => {
        match try_parse::<$t>(tokenstream!($s, $e), $s) {
            Ok(item) => item,
            Err(err) => {
                println!("could not parse {} from {}: {}", stringify!($t), $s, err);
                $e += 1;
                continue
            }
        }
    }
}

#[test]
fn parse_args() {
    let tests: &[(&str, &str, bool, bool)] = &[
        // parameters                   generic         path    error
        ("T -> i32, u32",               "T",            true,   false),
        ("my::U -> my::T<u32>",         "my::U",        true,   false),
        ("T -> Box<X>",                 "T",            true,   false),
        ("T -> Box<X>, &X, &mut X",     "T",            false,  false),
        ("T::U<V::W> -> X, Y",          "T::U<V::W>",   true,   false),
        ("T ->",                        "",             true,   true),
        ("[&T] -> [&mut T]",            "",             false,  true),
    ];
    let mut error = 0;
    for (idx, &(string, generic, path, parse_error)) in tests.iter().enumerate() {
        let report = format!("test #{idx} on '{string}': ");
        let stream = tokenstream!(string, error);
        // tests Subst::parse
        let mut new_error = true;
        match try_parse::<TraitGen>(stream, string) {
            Ok(subst) => {
                match () {
                    _ if parse_error =>
                        println!("{report}expecting parse error"),
                    _ if pathname(&subst.args) != generic =>
                        println!("{report}expecting generic '{}' instead of '{}'", generic, pathname(&subst.args)),
                    _ if subst.types.iter().all(|ty| matches!(ty, Type::Path(_))) != path =>
                        println!("{report}expecting {} mode", if path { "path" } else { "type" }),
                    _ => new_error = false
                }
            }
            Err(e) => {
                if !parse_error {
                    println!("{report}parse error (Subst):\n{e}");
                } else {
                    new_error = false;
                }
            }
        }
        if !new_error {
            // tests TraitGen::parse
            new_error = true;
            let stream = tokenstream!(&string, error);
            match try_parse::<TraitGen>(stream, &string) {
                Ok(params) => {
                    match () {
                        _ if parse_error =>
                            println!("{report}expecting parse error"),
                        _ if pathname(&params.args) != generic =>
                            println!("{report}expecting generic '{}' instead of '{}'", generic, pathname(&params.args)),
                        _ => new_error = false
                    }
                }
                Err(e) => {
                    if !parse_error {
                        println!("{report}parse error (TraitGen):\n{e}");
                    } else {
                        new_error = false;
                    }
                }
            }
        }
        if new_error {
            error += 1;
        };
    }
    assert!(error == 0, "{} error(s)", error);
}

#[test]
fn test_path_prefix_len() {
    let tests = &[
        // prefix           full                # segments
        ("T",               "T",                Some(1)),
        ("T",               "T::U",             Some(1)),
        ("T",               "T<U>",             Some(1)),
        ("T",               "U",                None),
        ("T",               "::T",              None),
        ("T",               "U::T",             None),
        ("T",               "U<T>",             None),
        ("T::U",            "T::U",             Some(2)),
        ("T::U",            "T::U::V",          Some(2)),
        ("T<U>",            "T",                None),
        ("T<U>",            "T<U>::V",          Some(1)),
        ("T<U>",            "T<U::X>::V",       None),
    ];
    let mut error = 0;
    for (idx, &(prefix, full, exp_len)) in tests.iter().enumerate() {
        let report = format!("test #{idx} on '{prefix}' in '{full}': ");
        let prefix_path = parse_str!(Path, prefix, error);
        let full_path = parse_str!(Path, full, error);
        let len = path_prefix_len(&prefix_path, &full_path);
        if len != exp_len {
            println!("{report}expecting {exp_len:?} instead of {len:?}");
            error += 1;
        }
    }
    assert!(error == 0, "{} error(s)", error);
}

#[test]
fn test_replace_str() {
    assert_eq!(replace_str("ab cd ab ef", "ab", "X"), Some("X cd X ef".to_string()));
}

mod test_parse_parameters {
    use proc_macro2::TokenStream;
    use std::str::FromStr;
    use syn::parse::{Parse, ParseStream};
    use syn::Type;
    use crate::{parse_parameters, pathname, ArgType};

    struct ArgsResult {
        args: ArgType,
        types: Vec<Type>,
        is_negated: bool,
    }
    
    impl std::fmt::Debug for ArgsResult {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "ArgsResult {{ args: {:?}, types: [{}], is_negated: {} }}", 
                   self.args, 
                   self.types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", "), 
                   self.is_negated
            )
        }
    }
    
    struct CondWrapper(ArgsResult);
    
    impl Parse for ArgsResult {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            match parse_parameters(input, false) {
                Ok((args, types, is_negated)) => Ok(ArgsResult { args, types, is_negated }),
                Err(e) => Err(e),
            }
        }
    }
    
    impl Parse for CondWrapper {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            match parse_parameters(input, true) {
                Ok((args, types, is_negated)) => Ok(CondWrapper(ArgsResult { args, types, is_negated })),
                Err(e) => Err(e),
            }
        }
    }
    
    
    #[test]
    fn test1() {
        const VERBOSE: bool = false;
        let tests = vec![
            (false, "T -> u8, u16",           Some("ArgsResult { args: Tuples(T), types: [u8, u16], is_negated: false }")),
            (false, "T, U -> u8, u16, u32",   Some("ArgsResult { args: Tuples(T, U), types: [u8, u16, u32], is_negated: false }")),
            (false, "T != U -> u8, u16, u32", Some("ArgsResult { args: Permutations(T, U), types: [u8, u16, u32], is_negated: false }")),
            (false, "T !< U -> u8, u16, u32", Some("ArgsResult { args: StrictOrder(T, U), types: [u8, u16, u32], is_negated: false }")),
            (false, "T =< U -> u8, u16, u32", Some("ArgsResult { args: NonStrictOrder(T, U), types: [u8, u16, u32], is_negated: false }")),
            (true, "T in u8, u16",            Some("ArgsResult { args: Cond(T), types: [u8, u16], is_negated: false }")),
        ];
        for (is_cond, string, expected) in tests {
            let token_stream = TokenStream::from_str(string).expect(&format!("can't create tokens from '{string}'"));
            let args_maybe = if is_cond {
                match syn::parse2::<CondWrapper>(token_stream) {
                    Ok(types) => Some(types.0),
                    Err(_err) => None,
                }
            } else {
                match syn::parse2::<ArgsResult>(token_stream) {
                    Ok(types) => Some(types),
                    Err(_err) => None,
                }
            };
            if VERBOSE {
                if let Some(ref args) = args_maybe {
                    println!("{string}: {args:?}");
                }
            }
            let result = args_maybe.map(|a| format!("{a:?}"));
            assert_eq!(result, expected.map(|s| s.to_string()), "test {string} failed");
        }
    }
}