// Copyright (c) 2025 Redglyph (@gmail.com). All Rights Reserved.
//
// Attribute argument parsing and related objects. Independent of proc_macro.

use std::collections::HashSet;
use std::fmt::{Debug, Formatter};
use proc_macro2::{Punct, Spacing};
use quote::{ToTokens, TokenStreamExt};
use syn::{bracketed, token, Error, ExprPath, Path, Token, Type};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use crate::utils::pathname;

#[derive(Clone)]
/// Variants of attribute left-hand-side arguments.
pub(crate) enum ArgType {
    None,
    /// Conditional argument. Must be a general `Type` because it's interchangeable with the right-hand side
    /// types. When this attribute is processed by `#[trait_gen]`, it's replaced by a type.
    ///
    /// - `#[trait_gen_if(T in U)`
    Cond(Type),
    /// List of arguments from which all permutations with repetition in a list are generated
    /// (it can have one or more arguments).
    ///
    /// The types in the list are not verified, so if the same type is present multiple times in the list,
    /// instances where the two arguments have the same type will be generated.
    ///
    /// Example:
    /// - `#[trait_gen(T -> u8, u16)]`
    ///
    ///   (T) = (u8), (u16)
    /// - `#[trait_gen(T, U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u8), (u8, u16), (u8, u32), (u16, u8), (u16, u16), (u16, u32) , ...
    Tuple(Vec<Path>),
    /// Pair of arguments from which all 2-permutations in a list are generated.
    ///
    /// The types in the list are not verified, so if the same type is present multiple times in the list,
    /// instances where the two arguments have the same type will be generated.
    ///
    /// Example:
    /// - `#[trait_gen(T != U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u16), (u8, u32), (u16, u8), (u16, u32), (u32, u8), (u32, u16)
    Permutation(Path, Path),
    /// Pair of arguments from which all 2-permutations with strict order in a list are generated.
    /// In other words, the position of the first argument is lower than the position of the second.
    ///
    /// A typical use is when you can safely combine integers with fewer bits into an integer with more bits
    /// but not the other way around.
    ///
    /// The types in the list are not verified, so if the same type is present multiple times in the list,
    /// instances where the two arguments have the same type will be generated.
    ///
    /// Example:
    /// - `#[trait_gen(T < U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u16), (u8, u32), (u16, u32)
    StrictOrder(Path, Path),
    /// Pair of arguments from which all 2-permutations with non-strict order in a list are generated.
    /// In other words, the position of the first argument is lower than or equal to the position of the second.
    ///
    /// A typical use is when you can safely convert an integer with fewer bits to an integer with
    /// at least as many bits but not the other way around.
    ///
    /// The types in the list are not verified, so if the same type is present multiple times in the list,
    /// instances where the two arguments have the same type will be generated.
    ///
    /// Example:
    /// - `#[trait_gen(T <= U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u8), (u8, u16), (u8, u32), (u16, u16), (u16, u32), (u32, u32)
    NonStrictOrder(Path, Path),
}

impl ToTokens for ArgType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            ArgType::None => {}
            ArgType::Cond(ty) => ty.to_tokens(tokens),
            ArgType::Tuple(paths) => tokens.append_separated(paths, Punct::new(',', Spacing::Alone)),
            ArgType::Permutation(path1, path2) => {
                path1.to_tokens(tokens);
                tokens.append(Punct::new('!', Spacing::Joint));
                tokens.append(Punct::new('=', Spacing::Alone));
                path2.to_tokens(tokens);
            }
            ArgType::StrictOrder(path1, path2) => {
                path1.to_tokens(tokens);
                tokens.append(Punct::new('!', Spacing::Joint));
                tokens.append(Punct::new('<', Spacing::Alone));
                path2.to_tokens(tokens);
            }
            ArgType::NonStrictOrder(path1, path2) => {
                path1.to_tokens(tokens);
                tokens.append(Punct::new('=', Spacing::Joint));
                tokens.append(Punct::new('<', Spacing::Alone));
                path2.to_tokens(tokens);
            }
        }
    }
}

impl Debug for ArgType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ArgType::None => write!(f, "None"),
            ArgType::Cond(c) => write!(f, "Cond({})", pathname(c)),
            ArgType::Tuple(a) => write!(f, "Tuple({})", a.iter().map(pathname).collect::<Vec<_>>().join(", ")),
            ArgType::Permutation(p1, p2) => write!(f, "Permutation({}, {})", pathname(p1), pathname(p2)),
            ArgType::StrictOrder(p1, p2) => write!(f, "StrictOrder({}, {})", pathname(p1), pathname(p2)),
            ArgType::NonStrictOrder(p1, p2) => write!(f, "NonStrictOrder({}, {})", pathname(p1), pathname(p2)),
        }
    }
}

//==============================================================================
// Attribute types

#[derive(Clone, Debug)]
/// Attribute data used to substitute arguments in inner `trait_gen`/`type_gen` attributes
pub(crate) struct TraitGen {
    /// generic arguments
    pub args: ArgType,
    /// types that replace the generic argument
    pub types: Vec<Type>,
}

#[derive(Clone)]
/// Attribute data used in `trait_gen_if`/`type_gen_if` conditionals. We store the generic
/// argument and the types as [String], to make the comparison easier.
pub(crate) struct CondParams {
    /// generic argument
    pub generic_arg: Type,
    /// if the argument matches at least one of those types, the attached code is enabled
    pub types: HashSet<Type>,
    /// negate the condition: the condition becomes true when the argument doesn't match any of the `types`
    pub is_negated: bool
}

//==============================================================================
// Attribute argument parsing

/// Parses the attribute arguments, and extracts the generic argument and the types that must substitute it.
///
/// There are two main syntax formats:
/// - `T -> Type1, Type2, Type3` with variations like `T, U -> ...`, `T != U -> ...`, etc.
/// - `T in [Type1, Type2, Type3]` or `T in Type1, Type2, Type3` (when `is_conditional` is true)
///
/// The `is_conditional` parameter forces the "in" format and allows the negation: `!T in Type1, Type2, Type3`.
/// It also returns a `Type` argument (`SubstType::Type`) instead of a `Path` because the trait-gen attribute
/// will replace it by a type.
///
/// Returns (args, types, is_negated), where
/// - `args` contains the generic arguments `T`, `U`, ... and the type of permutation (`,`, `!=`, `<`, or `<=`)
/// - `types` is a vector of parsed `Type` items: `Type1, Type2, Type3`
/// - `is_negated` is true if the `!T in` format was found instead of `T in` (when `is_conditional` is true)
pub(crate) fn parse_arguments(input: ParseStream, is_conditional: bool) -> syn::parse::Result<(ArgType, Vec<Type>, bool)> {
    let is_negated = is_conditional && input.peek(Token![!]) && input.parse::<Token![!]>().is_ok();
    let args = if is_conditional {
        ArgType::Cond(input.parse::<Type>()?)
    } else {
        // Determines the format of the left-hand arguments.
        // ExprPath is used instead of Path in order to force a turbofish syntax; this allows the use
        // of '<' as a separator between arguments: "U < V", or if a generic argument is really required,
        // "U::<X> < V". Without that, it wouldn't be possible to parse a path followed by a '<' token.
        let path1 = input.parse::<ExprPath>()?.path;
        if input.peek(Token![,]) && input.parse::<Token![,]>().is_ok() {
            // Tuple: "W, X, Y -> Type1, Type2"
            let mut list_args = vec![path1];
            loop {
                let p = input.parse::<ExprPath>()?.path;
                list_args.push(p);
                if input.peek(Token![,]) {
                    _ = input.parse::<Token![,]>();
                } else {
                    break;
                }
            }
            ArgType::Tuple(list_args)
        } else if input.peek(Token![!]) && input.parse::<Token![!]>().is_ok() {
            // Permutation: "W != X -> Type1, Type2"
            input.parse::<Token![=]>()?;
            ArgType::Permutation(path1, input.parse::<Path>()?)
        } else if input.peek(Token![<]) && input.parse::<Token![<]>().is_ok() {
            // Permutation with strict or non-strict order: "W < X -> Type1, Type2" or "W <= X -> Type1, Type2"
            if input.peek(Token![=]) && input.parse::<Token![=]>().is_ok() {
                ArgType::NonStrictOrder(path1, input.parse::<Path>()?)
            } else {
                ArgType::StrictOrder(path1, input.parse::<Path>()?)
            }
        } else {
            // that something else must be '->', so we return a single "normal" argument
            ArgType::Tuple(vec![path1])
        }
    };

    if is_conditional {
        input.parse::<Token![in]>()?;
    } else {
        input.parse::<Token![->]>()?;
    }

    // collects the right-hand arguments depending on format
    let types: Vec<Type>;
    let vars = if is_conditional {
        // brackets are optional:
        if input.peek(token::Bracket) {
            let content;
            bracketed!(content in input);
            let inner_vars: ParseStream = &content;
            Punctuated::<Type, Token![,]>::parse_terminated(inner_vars)?
        } else {
            Punctuated::<Type, Token![,]>::parse_terminated(input)?
        }
    } else {
        Punctuated::<Type, Token![,]>::parse_terminated(input)?
    };
    types = vars.into_iter().collect();
    if types.is_empty() {
        return Err(Error::new(input.span(), "expected type"));
    }
    Ok((args, types, is_negated))
}

/// Attribute argument parser used for the procedural macro being processed
impl Parse for TraitGen {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let (args, types, _) = parse_arguments(input, false)?;
        Ok(TraitGen { args, types })
    }
}

/// Attribute argument parser used for the inner conditional attributes
impl Parse for CondParams {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let (args, types, is_negated) = parse_arguments(input, true)?;
        let generic_arg = if let ArgType::Cond(t) = args { t } else { panic!("can't happen") };
        Ok(CondParams {
            generic_arg,
            types: types.into_iter().collect(),
            is_negated,
        })
    }
}
