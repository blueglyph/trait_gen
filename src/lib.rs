// Copyright 2023 Redglyph
//
// Macros and helpers. Contains procedural macros so nothing else than macros can be exported.

//! This crate provides attribute macros that generate the attached implementation for all the
//! types given in argument. It was first intended for trait implementations, hence the crate name,
//! but it can also be used for any generic implementation.
//!
//! ## Usage
//! The attribute is placed before the pseudo-generic code to implement. The _generic arguments_
//! are given first, followed by a right arrow (`->`) and a list of types that will replace the
//! argument in the generated implementations:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # struct Type1; struct Type2; struct Type3;
//! # trait Trait {}
//! #[trait_gen(T -> Type1, Type2, Type3)]
//! impl Trait for T {
//!     // ...
//! }
//! ```
//!
//! The attribute macro successively substitutes the generic argument `T` in the code with
//! the given types (`Type1`, `Type2`, `Type3`) to generate each implementation.
//!
//! All the [type paths](https://doc.rust-lang.org/reference/paths.html#paths-in-types) beginning
//! with `T` in the code have that part replaced. For example, `T::default()` generates
//! `Type1::default()`, `Type2::default()` and so on, but `super::T` is unchanged. Similarly, all
//! the [types](https://doc.rust-lang.org/reference/types.html) including `T` in the code have that
//! part replaced; for example, `&T` or `Box<T>`.
//!
//! The compiler will trigger an error if the resulting code is wrong. For example
//! `#[trait_gen(T -> u64, f64)]` cannot be applied to `let x: T = 0;` because `0` is not a valid
//! floating-point literal.
//!
//! Finally, the actual type of `T` replaces any occurrence of `${T}` in doc comments, macros, and
//! string literals.
//!
//! _Notes:_
//! - _Using the letter "T" is not mandatory; any type path will do. For example, `g::Type` is fine
//! too. But to make it easy to read and similar to a generic implementation, short upper-case identifiers
//! are preferred._
//! - _If a `<..>` is required in the generic argument, the
//! [turbofish syntax](https://doc.rust-lang.org/reference/paths.html#r-paths.expr.turbofish) must be used.
//! For example, use `#[trait_gen(T::<U> -> ...)` and not `#[trait_gen(T<U> -> ...)`._
//! - _`type_gen` is a synonym attribute that can be used instead of `trait_gen`. This can be disabled with
//! the `no_type_gen` feature, in case it conflicts with another 3rd-party attribute._
//! - _There is no escape code to avoid the substitution in string literals; if you need `${T}` for another
//! purpose and you don't want it to be replaced, you can use this work-around:
//! `#[doc = concat!("my ${", "T} variable")]`. Or you can choose another generic argument, like `U` or `my::T`._
//! - _More complex formats with several arguments and conditions are shown in later examples._
//!
//! Here is a simple example:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # trait MyLog { fn my_log2(self) -> u32; }
//! #[trait_gen(T -> u8, u16, u32, u64, u128)]
//! impl MyLog for T {
//!     fn my_log2(self) -> u32 {
//!         T::BITS - 1 - self.leading_zeros()
//!     }
//! }
//! ```
//!
//! The `trait_gen` attribute generates the following code by replacing `T` with the types given as
//! arguments:
//!
//! ```rust
//! # trait MyLog { fn my_log2(self) -> u32; }
//! impl MyLog for u8 {
//!     fn my_log2(self) -> u32 {
//!         u8::BITS - 1 - self.leading_zeros()
//!     }
//! }
//!
//! impl MyLog for u16 {
//!     fn my_log2(self) -> u32 {
//!         u16::BITS - 1 - self.leading_zeros()
//!     }
//! }
//!
//! // ... and so on for the remaining types
//! ```
//!
//! ## Compositions
//! `trait_gen` also replaces the content of inner attributes, so it's possible to chain them
//! and extend the above example to references and smart pointers for all the `T` types:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # trait MyLog { fn my_log2(self) -> u32; }
//! # #[trait_gen(T -> u8, u16, u32, u64, u128)]
//! # impl MyLog for T {
//! #     fn my_log2(self) -> u32 {
//! #         T::BITS - 1 - self.leading_zeros()
//! #     }
//! # }
//! #[trait_gen(T -> u8, u16, u32, u64, u128)]
//! #[trait_gen(U -> &T, &mut T, Box<T>)]
//! impl MyLog for U {
//!     /// Logarithm base 2 for `${U}`
//!     fn my_log2(self) -> u32 {
//!         MyLog::my_log2(*self)
//!     }
//! }
//! ```
//!
//! ## Tuples and Conditional Generation
//! A more concise format can be used when several arguments share the type lists (in other
//! words, when we need _permutations with repetitions_, or _tuples_):
//!
//! ```rust,ignore
//! #[trait_gen(T, U -> u8, u16, u32)]
//! ```
//!
//! In the following example, we also show the conditional attribute `trait_gen_if`, which
//! offers more flexibility in the implementations. The condition has the general format
//! `<argument> in <types>`, or its negation, `!<argument> in <types>`. The code is respectively
//! included or skipped when the argument is identical to one of the types.
//!
//! ```rust
//! use trait_gen::{trait_gen, trait_gen_if};
//!
//! #[derive(Clone, PartialEq, Debug)]
//! struct Wrapper<T>(T);
//!
//! #[trait_gen(T, U -> u8, u16, u32)]
//! // The types T and U must be different to avoid the compilation error
//! // "conflicting implementation in crate `core`: impl<T> From<T> for T"
//! #[trait_gen_if(!T in U)]
//! impl From<Wrapper<U>> for Wrapper<T> {
//!     /// converts Wrapper<${U}> to Wrapper<${T}>
//!     fn from(value: Wrapper<U>) -> Self {
//!         Wrapper(T::try_from(value.0)
//!             .expect(&format!("overflow when converting {} to ${T}", value.0)))
//!     }
//! }
//! ```
//!
//! That will give us all the conversions from/to `u8`, `u16`, and `u32`, except from the
//! same type since they're already covered by a blanket implementation in the standard library.
//! `trait_gen_if` is also very useful for selecting constants or removing methods depending on the
//! implementated type.
//!
//! _Notes:_
//! - _The number of generic arguments is not limited in this particular form, though it's arguably
//! hard to find relevant cases where more than two are required._
//! - _We've seen earlier that `type_gen` was a synonym of `trait_gen`. For the sake of
//! coherency, a `type_gen_if` is provided as a synonym of `trait_gen_if`, too._
//!
//! ## Other Permutations
//! The implementation above could have been written more concisely with a _2-permutation_, where
//! `T != U`:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! #
//! # #[derive(Clone, PartialEq, Debug)]
//! # struct Wrapper<T>(T);
//! #
//! #[trait_gen(T != U -> u8, u16, u32)]
//! impl From<Wrapper<U>> for Wrapper<T> {
//!     /// converts Wrapper<${U}> to Wrapper<${T}>
//!     fn from(value: Wrapper<U>) -> Self {
//!         Wrapper(T::try_from(value.0)
//!             .expect(&format!("overflow when converting {} to ${T}", value.0)))
//!     }
//! }
//! ```
//!
//! If we want to generate all the conversions from smaller integers to bigger integers,
//! similarly to what is done in the [standard library](https://github.com/rust-lang/rust/blob/1.86.0/library/core/src/convert/num.rs#L514-L526)
//! (with a cascade of declarative macros), we can use a _2-permutation with strict order_,
//! meaning that `index(T) < index(U)`—remember we can't convert to the same type
//! because it conflicts with the blanket implementation in `core`.
//!
//! This will generate the code for `(T, U)` = `(u8, u16)`, `(u8, u32)`, and `(u16, u32)`
//! (picture a triangle):
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! #
//! # #[derive(Clone, PartialEq, Debug)]
//! # struct Wrapper<T>(T);
//! #
//! #[trait_gen(T < U -> u8, u16, u32)]
//! impl From<Wrapper<T>> for Wrapper<U> {
//!     /// converts Wrapper<${T}> to Wrapper<${U}>
//!     fn from(value: Wrapper<T>) -> Self {
//!         Wrapper(U::from(value.0))
//!     }
//! }
//! ```
//!
//!
//! The _non-strict order_, where `index(T) <= index(U)`, also exists for cases like
//! adding from another integer which has a smaller or equal length. This will generate
//! the code for `(T, U)` = `(u8, u8)`, `(u8, u16)`, `(u8, u32)`, `(u16, u16)`, `(u16, u32)`,
//! and `(u32, u32)`.
//!
//! ```rust
//! # use std::ops::Add;
//! # use trait_gen::trait_gen;
//! #
//! # #[derive(Clone, PartialEq, Debug)]
//! # struct Wrapper<T>(T);
//! #
//! #[trait_gen(T <= U -> u8, u16, u32)]
//! impl Add<Wrapper<T>> for Wrapper<U> {
//!     type Output = Wrapper<U>;
//!
//!     fn add(self, rhs: Wrapper<T>) -> Self::Output {
//!         Wrapper::<U>(self.0 + <U>::from(rhs.0))
//!     }
//! }
//! ```
//!
//! _Notes:_
//! - _`!=`, `<`, and `<=` are limited to two generic arguments._
//!
//! That covers all the forms of these attributes. For more examples, look at the crate's
//! [integration tests](https://github.com/blueglyph/trait_gen/blob/v2.0.0/tests/integration.rs).
//!
//! ## Limitations
//!
//! * The procedural macro of the `trait_gen` attribute can't handle scopes, so it doesn't support any
//! type declaration with the same literal as the generic argument. For instance, this code fails to compile
//! because of the generic function:
//!
//!   ```rust, ignore
//!   #[trait_gen(T -> u64, i64, u32, i32)]
//!   impl AddMod for T {
//!       type Output = T;
//!
//!       fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output {
//!           fn int_mod<T: Num> (a: T, m: T) -> T { // <== ERROR, conflicting 'T'
//!               a % m
//!           }
//!           int_mod(self + rhs, modulo)
//!       }
//!   }
//!   ```
//!
//! * The generic argument must be a [type path](https://doc.rust-lang.org/reference/paths.html#paths-in-types);
//! it cannot be a more complex type like a reference or a slice. So you can use `g::T<U> -> ...`
//! but not `&T -> ...`.

mod tests;

use std::collections::HashSet;
use std::fmt::{Debug, Formatter};
use proc_macro::TokenStream;
use proc_macro2::{Punct, Spacing};
use proc_macro_error::{proc_macro_error, abort};
use quote::{quote, ToTokens, TokenStreamExt};
use syn::{Generics, GenericParam, Token, File, TypePath, Path, PathArguments, Expr, Lit, LitStr, ExprLit, Macro, parse_str, Attribute, PathSegment, GenericArgument, Type, Error, bracketed, MetaList, token, ExprPath};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::PathSep;
use syn::visit_mut::VisitMut;
#[allow(unused_imports)]
use syn::parse2; // wrongly detected as unused

// For verbose debugging
const VERBOSE: bool = false;
const VERBOSE_TF: bool = false;

//==============================================================================
// Attributes that may be inside the content scanned by trait-gen, and which need
// to be processed (the other attributes, either standard or from 3rd-party crates
// are attached normally on the code generated by trait-gen).

// Embedded trait-gen attributes (trait-gen will check for types / paths that must
// be changed).
// Note: when the feature "type_gen" is disabled, we avoid matching "type_gen" by
//       making both constants equal (those constants are used in a match statement).
const TRAIT_GEN: &str = "trait_gen";
const TYPE_GEN: &str = if cfg!(feature = "no_type_gen") { TRAIT_GEN } else { "type_gen" };

// Attributes for conditional implementation.
// Note: when the feature "type_gen" is disabled, we avoid matching "type_gen_if" by
//       making both constants equal (those constants are used in a match statement).
const TRAIT_GEN_IF: &str = "trait_gen_if";
const TYPE_GEN_IF: &str = if cfg!(feature = "no_type_gen") { TRAIT_GEN_IF } else { "type_gen_if" };

//==============================================================================
// Misc types and their implementations

#[derive(Clone, PartialEq)]
/// Substitution item, either a Path (`super::Type`) or a Type (`&mut Type`)
enum SubstType {
    Path(Path),
    Type(Type)
}

impl ToTokens for SubstType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            SubstType::Path(path) => path.to_tokens(tokens),
            SubstType::Type(ty) => ty.to_tokens(tokens)
        }
    }
}

impl Debug for SubstType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SubstType::Path(p) => write!(f, "Path({})", pathname(p)),
            SubstType::Type(t) => write!(f, "Type({})", pathname(t)),
        }
    }
}

#[derive(Clone)]
/// Variants of attribute left-hand-side arguments.
enum ArgType {
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
            ArgType::Tuple(a) => write!(f, "Tuple({})", a.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", ")),
            ArgType::Permutation(p1, p2) => write!(f, "Permutation({}, {})", pathname(p1), pathname(p2)),
            ArgType::StrictOrder(p1, p2) => write!(f, "StrictOrder({}, {})", pathname(p1), pathname(p2)),
            ArgType::NonStrictOrder(p1, p2) => write!(f, "NonStrictOrder({}, {})", pathname(p1), pathname(p2)),
        }
    }
}

/// This type is only used to implement the VisitMut trait.
struct TurboFish;

/// Adds the turbofish double-colon whenever possible to avoid post-substitution problems.
///
/// The replaced part may be an expression requiring it, or a type that doesn't require the
/// double-colon but accepts it. Handling both cases would be complicated so we always include it.
impl VisitMut for TurboFish {
    fn visit_path_mut(&mut self, node: &mut Path) {
        if VERBOSE_TF {
            println!("TURBOF: path '{}'", pathname(node));
        }
        for segment in &mut node.segments {
            if let PathArguments::AngleBracketed(generic_args) = &mut segment.arguments {
                generic_args.colon2_token = Some(PathSep::default());
            }
        }
    }
}

//==============================================================================
// Main substitution types (VisitMut/Parse implementations defined further down)

#[derive(Clone, Debug)]
/// Attribute data used to substitute arguments in inner `trait_gen`/`type_gen` attributes
struct TraitGen {
    /// generic arguments
    args: ArgType,
    /// types that replace the generic argument
    types: Vec<Type>,
}

#[derive(Clone)]
/// Attribute substitution data used to replace the generic argument in `generic_arg` with the
/// types in `new_types`.
struct Subst {
    /// generic argument to replace
    generic_arg: Path,
    /// types that replace the generic argument
    types: Vec<SubstType>,
    /// Path substitution items if true, Type items if false
    is_path: bool,
    /// Context stack, cannot substitue paths when last is false (can substitute if empty)
    can_subst_path: Vec<bool>,
}

#[derive(Clone)]
/// Attribute data used in `trait_gen_if`/`type_gen_if` conditionals. We store the generic
/// argument and the types as [String], to make the comparison easier.
struct CondParams {
    /// generic argument
    generic_arg: Type,
    /// if the argument matches at least one of those types, the attached code is enabled
    types: HashSet<Type>,
    /// negate the condition: the condition becomes true when the argument doesn't match any of the `types`
    is_negated: bool
}

impl Subst {
    fn from_trait_gen(attribute: TraitGen, generic_arg: Path) -> Self {
        let (is_path, types) = to_subst_types(attribute.types);
        Subst {
            generic_arg,
            types,
            is_path,
            can_subst_path: vec![],
        }
    }

    fn can_subst_path(&self) -> bool {
        *self.can_subst_path.last().unwrap_or(&true)
    }

    /// Gives a helpful list of type names that might be used in a substitution list.
    fn get_example_types(&self) -> String {
        // This is called for error messages, which happen only during the first visit_mut pass over
        // the inner attributes: we know that Subst still has all the types in `self.new_types`.
        let mut examples = self.types.iter().map(|t| pathname(t)).take(3).collect::<Vec<_>>();
        while examples.len() < 3 {
            examples.push(format!("Type{}", examples.len() + 1));
        }
        examples.join(", ")
    }
}

impl Debug for Subst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "PathTypes {{ generic_arg: {}, types: [{}], is_path: {}, enabled: {} }}",
               pathname(&self.generic_arg),
               self.types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", "),
               self.is_path,
               self.can_subst_path.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ")
        )
    }
}

//==============================================================================
// Helper functions and traits

/// Creates a string from a tokenizable item and removes the annoying spaces.
fn pathname<T: ToTokens>(path: &T) -> String {
    path.to_token_stream().to_string()
        .replace(" :: ", "::")
        .replace(" <", "<")
        .replace("< ", "<")
        .replace(" >", ">")
        .replace("> ", ">")
        .replace("& ", "&")
        .replace(", ", ",")
        .replace(") ", ")")
        .replace(" ;", ";")
        .replace("; ", ";")
}

trait NodeMatch {
    /// Checks if the `self` node is a prefix of `other`.
    fn match_prefix(&self, other: &Self) -> bool;
}

impl NodeMatch for GenericArgument {
    /// Compares both generic arguments, disregarding lifetime argument names
    fn match_prefix(&self, other: &Self) -> bool {
        if let GenericArgument::Lifetime(_) = self {
            // ignoring the actual lifetime ident
            matches!(other, GenericArgument::Lifetime(_))
        } else {
            self == other
        }
    }
}

impl NodeMatch for PathSegment {
    /// Compares both segments and returns true if `self` is similar to `seg_pat`, disregarding
    /// * any "turbofish" difference when there are angle bracket arguments
    /// * the arguments if `seg_pat` doesn't have any
    fn match_prefix(&self, seg_pat: &PathSegment) -> bool {
        self.ident == seg_pat.ident && match &seg_pat.arguments {
            PathArguments::None =>
                true, //matches!(seg_pat.arguments, PathArguments::None),
            PathArguments::AngleBracketed(ab_pat) => {
                if let PathArguments::AngleBracketed(ab) = &self.arguments {
                    // ignoring turbofish in colon2_token
                    ab.args.len() == ab_pat.args.len() &&
                        ab.args.iter().zip(&ab_pat.args).all(|(a, b)| a.match_prefix(b))
                } else {
                    false
                }
            }
            PathArguments::Parenthesized(p_pat) => {
                if let PathArguments::Parenthesized(p) = &self.arguments {
                    p == p_pat
                } else {
                    false
                }
            }
        }
    }
}

/// Compares two type paths and, if `prefix` is a prefix of `full_path`, returns the number of
/// matching segments.
fn path_prefix_len(prefix: &Path, full_path: &Path) -> Option<usize> {
    let prefix_len = prefix.segments.len();
    if full_path.leading_colon == prefix.leading_colon && full_path.segments.len() >= prefix_len {
        for (seg_full, seg_prefix) in full_path.segments.iter().zip(&prefix.segments) {
            if !seg_full.match_prefix(seg_prefix) {
                return None;
            }
        }
        return Some(prefix_len)
    }
    None
}

/// Replaces the pattern `pat` with `repl` in `string`. Returns `Some(resulting string)` if
/// the string changed, None if there was no replacement.
fn replace_str(string: &str, pat: &str, repl: &str) -> Option<String> {
    if string.contains(pat) {
        Some(string.replace(pat, repl))
    } else {
        None
    }
}

/// Converts a list of `Type` to a list of `SubstType`, making them all `Path` if possible,
/// otherwise all `Type`.
fn to_subst_types(mut types: Vec<Type>) -> (bool, Vec<SubstType>) {
    let mut visitor = TurboFish;
    for ty in types.iter_mut() {
        visitor.visit_type_mut(ty);
    }
    let is_path = types.iter().all(|ty| matches!(ty, Type::Path(_)));
    let subst_types = types.into_iter()
        .map(|ty|
            if is_path {
                if let Type::Path(p) = ty {
                    SubstType::Path(p.path)
                } else {
                    panic!("this should match Type::Path: {:?}", ty)
                }
            } else {
                SubstType::Type(ty)
            })
        .collect::<Vec<_>>();
    (is_path, subst_types)
}

//==============================================================================
// Main substitution code

impl VisitMut for Subst {
    fn visit_attribute_mut(&mut self, node: &mut Attribute) {
        // Takes the last segment in case there's a specific path to the attribute. This means we don't support other attributes
        // with the same name inside the outer attribute, but it shouldn't be a problem as long as they could be renamed in the `use`
        // declaration (in the unlikely event that another attribute shared the same name).
        if let Some(PathSegment { ident, .. }) = node.path().segments.last() {
            let ident = ident.to_string();
            match ident.as_str() {
                // conditional pseudo-attribute (TYPE_GEN_IF == TRAIT_GEN_IF when type_gen is disabled)
                TRAIT_GEN_IF | TYPE_GEN_IF => {
                    // checks that the syntax is fine and performs the type substitutions if required
                    match node.parse_args::<CondParams>() {
                        Ok(cond) => {
                            let mut output = proc_macro2::TokenStream::new();
                            if VERBOSE { println!("- {} -> {}", pathname(&self.generic_arg), pathname(self.types.first().unwrap())); }
                            let mut g = cond.generic_arg;
                            self.visit_type_mut(&mut g);
                            if cond.is_negated {
                                output.extend(quote!(!#g in));
                            } else {
                                output.extend(quote!(#g in));
                            }
                            let mut first = true;
                            for mut ty in cond.types {
                                // checks if substitutions must be made in that argument:
                                self.visit_type_mut(&mut ty);
                                if !first {
                                    output.extend(quote!(, ));
                                }
                                output.extend(quote!(#ty));
                                first = false;
                            }
                            let original = pathname(&node);
                            if let syn::Meta::List(MetaList { ref mut tokens, .. }) = node.meta {
                                if VERBOSE { println!("  {original} => {}", pathname(&output)); }
                                *tokens = output;
                                return;
                            } else {
                                // shouldn't happen
                                abort!(node.meta.span(), "invalid {} attribute format", ident;
                                    help = "The expected format is: #[{}({} -> {})]", ident, pathname(&self.generic_arg), self.get_example_types());
                            };
                        }
                        Err(err) => {
                            // gives a personalized hint
                            abort!(err.span(), err;
                                help = "The expected format is: #[{}({} in {})]", ident, pathname(&self.generic_arg), self.get_example_types());
                        }
                    };
                }
                // embedded trait-gen attributes
                TRAIT_GEN | TYPE_GEN => {
                    // Perform substitutions in the arguments of the inner attribute if necessary.
                    // #[trait_gen(U -> i32, u32)]     // <== self
                    // #[trait_gen(T -> &U, &mut U)]   // <== change 'U' to 'i32' and 'u32'
                    // impl Neg for T { /* .... */ }
                    match node.parse_args::<TraitGen>() {
                        Ok(mut types) => {
                            let mut output = proc_macro2::TokenStream::new();
                            // It would be nice to give a warning if the format of the attributes were different,
                            // once there is a way to generate custom warnings (an error for that seems too harsh).
                            let g = types.args;
                            output.extend(quote!(#g -> ));
                            let mut first = true;
                            for ty in &mut types.types {
                                // checks if substitutions must be made in that argument:
                                self.visit_type_mut(ty);
                                if !first {
                                    output.extend(quote!(, ));
                                }
                                output.extend(quote!(#ty));
                                first = false;
                            }
                            if let syn::Meta::List(MetaList { ref mut tokens, .. }) = node.meta {
                                *tokens = output;
                                return;
                            } else {
                                // shouldn't happen
                                abort!(node.meta.span(), "invalid {} attribute format", ident;
                                    help = "The expected format is: #[{}({} -> {})]", ident, pathname(&self.generic_arg), self.get_example_types());
                            };
                        }
                        Err(err) => {
                            // gives a personalized hint
                            abort!(err.span(), err;
                                help = "The expected format is: #[{}({} -> {})]", ident, pathname(&self.generic_arg), self.get_example_types());
                        }
                    };
                    
                }
                _ => ()
            }
        }
        syn::visit_mut::visit_attribute_mut(self, node);
    }

    fn visit_expr_mut(&mut self, node: &mut Expr) {
        let mut enabled = self.can_subst_path();
        match node {
            // allows substitutions for the nodes below, and until a new Expr is met:
            Expr::Call(_) => enabled = true,
            Expr::Cast(_) => enabled = true,
            Expr::Struct(_) => enabled = true,

            // 'ExprPath' is the node checking for authorization through ExprPath.path,
            // so the current 'enabled' is preserved: (see also visit_path_mut())
            Expr::Path(_) => { /* don't change */ }

            // all other expressions in general must disable substitution:
            _ => enabled = false,
        };
        self.can_subst_path.push(enabled);
        syn::visit_mut::visit_expr_mut(self, node);
        self.can_subst_path.pop();
    }

    fn visit_expr_lit_mut(&mut self, node: &mut ExprLit) {
        if let Lit::Str(lit) = &node.lit {
            // substitutes "${T}" in expression literals (not used in macros, see visit_macro_mut)
            if let Some(ts_str) = replace_str(
                &lit.to_token_stream().to_string(),
                &format!("${{{}}}", pathname(&self.generic_arg)),
                &pathname(self.types.first().unwrap()))
            {
                let new_lit: LitStr = parse_str(&ts_str).expect(&format!("parsing LitStr failed: {}", ts_str));
                node.lit = Lit::Str(new_lit);
            } else {
                syn::visit_mut::visit_expr_lit_mut(self, node);
            }
        }
    }

    fn visit_generics_mut(&mut self, i: &mut Generics) {
        if let Some(segment) = self.generic_arg.segments.first() {
            let current_ident = &segment.ident;
            for t in i.params.iter() {
                match &t {
                    GenericParam::Type(t) => {
                        if &t.ident == current_ident {
                            abort!(t.span(),
                                "Type '{}' is reserved for the substitution.", current_ident.to_string();
                                help = "Use another identifier for this local generic type."
                            );

                            // replace the 'abort!' above with this once it is stable:
                            //
                            // t.span().unwrap()
                            //     .error(format!("Type '{}' is reserved for the substitution.", self.current_type.to_string()))
                            //     .help("Use another identifier for this local generic type.")
                            //     .emit();
                        }
                    }
                    _ => {}
                }
            }
        }
        syn::visit_mut::visit_generics_mut(self, i);
    }

    fn visit_macro_mut(&mut self, node: &mut Macro) {
        // substitutes "${T}" in macros
        if let Some(ts_str) = replace_str(
            &node.tokens.to_string(),
            &format!("${{{}}}", pathname(&self.generic_arg)),
            &pathname(self.types.first().unwrap()))
        {
            let new_ts: proc_macro2::TokenStream = ts_str.parse().expect(&format!("parsing Macro failed: {}", ts_str));
            node.tokens = new_ts;
        } else {
            syn::visit_mut::visit_macro_mut(self, node);
        }
    }

    fn visit_path_mut(&mut self, path: &mut Path) {
        let path_name = pathname(path);
        let path_length = path.segments.len();
        if let Some(length) = path_prefix_len(&self.generic_arg, path) {
            // If U is both a constant and the generic argument, in an expression (so when
            // self.substitution_enabled() == false), we must distinguish two cases:
            // - U::MAX must be replaced (length < path_length)
            // - U or U.add(1) must stay
            if length < path_length || self.can_subst_path() {
                if VERBOSE { print!("[path] path: {} length = {}", path_name, length); }
                match self.types.first().unwrap() {
                    SubstType::Path(p) => {
                        let mut new_seg = p.segments.clone();
                        for seg in path.segments.iter().skip(length) {
                            new_seg.push(seg.clone());
                        }
                        // check if orphan arguments:
                        //     #[trait_gen(g::T -> mod::Name, ...) { ... g::T<'_> ... }
                        //     path     = g :: T   <'_>    len = 2, subst enabled
                        //     new_path = mod :: Name        len = 2
                        //  => new_seg  = mod :: Name<'_>
                        let nth_new_seg = new_seg.last_mut().unwrap();
                        let nth_seg = path.segments.iter().nth(length - 1).unwrap();
                        if nth_new_seg.arguments.is_empty() && !nth_seg.arguments.is_empty() {
                            nth_new_seg.arguments = nth_seg.arguments.clone();
                        }
                        path.segments = new_seg;
                        if VERBOSE { println!(" -> {}", pathname(path)); }
                    }
                    SubstType::Type(ty) => {
                        if VERBOSE { println!(" -> Path '{}' cannot be substituted by type '{}'", path_name, pathname(ty)); }
                        // note: emit-warning is unstable...
                        abort!(ty.span(), "Path '{}' cannot be substituted by type '{}'", path_name, pathname(ty));
                    }
                }
            } else {
                if VERBOSE { println!("disabled path: {}", path_name); }
                syn::visit_mut::visit_path_mut(self, path);
            }
        } else {
            if VERBOSE { println!("path: {} mismatch", path_name); }
            syn::visit_mut::visit_path_mut(self, path);
        }
    }

    fn visit_type_mut(&mut self, node: &mut Type) {
        if !self.is_path {
            match node {
                Type::Path(TypePath { path, .. }) => {
                    let path_name = pathname(path);
                    let path_length = path.segments.len();
                    if let Some(length) = path_prefix_len(&self.generic_arg, path) {
                        if /*length < path_length ||*/ self.can_subst_path() {
                            assert!(length == path_length, "length={length}, path_length={path_length}");
                            // must implement length < path_length if such a case can be found, but it's been elusive
                            if VERBOSE {
                                print!("[type] type path: {} length = {length}, path length = {path_length} {} -> ",
                                       path_name, if self.can_subst_path() { ", can_subst" } else { "" });
                            }
                            *node = if let SubstType::Type(ty) = self.types.first().unwrap() {
                                if VERBOSE { println!("{}", pathname(ty)); }
                                ty.clone()
                            } else {
                                panic!("found path item instead of type in SubstType")
                            };
                        }
                    } else {
                        syn::visit_mut::visit_type_mut(self, node);
                    }
                }
                _ => syn::visit_mut::visit_type_mut(self, node),
            }
        } else {
            syn::visit_mut::visit_type_mut(self, node);
        }
    }

    fn visit_type_path_mut(&mut self, typepath: &mut TypePath) {
        self.can_subst_path.push(true);
        let TypePath { path, .. } = typepath;
        if VERBOSE { println!("typepath: {}", pathname(path)); }
        syn::visit_mut::visit_type_path_mut(self, typepath);
        self.can_subst_path.pop();
    }
}

//==============================================================================
// Attribute argument processing

/// Parses the attribute arguments, and extracts the generic argument and the types that must substitute it.
///
/// There are two main syntax formats:
/// - `T -> Type1, Type2, Type3` with variations like `T, U -> ...`, `T != U -> ...`, etc.
/// - `T in [Type1, Type2, Type3]` or `T in Type1, Type2, Type3` (when `is_conditional` is true)
///
/// The `is_conditional` parameter forces the "in" format and allows a negation, `!T in Type1, Type2, Type3`.
/// It also returns a `Type` argument (`SubstType::Type`) instead of a `Path` because the trait-gen attribute
/// will replace it by a type.
///
/// Returns (args, types, is_negated), where
/// - `args` contains the generic arguments `T`, `U`, ... and the type of permutation (`,`, `!=`, `<`, or `<=`)
/// - `types` is a vector of parsed `Type` items: `Type1, Type2, Type3`
/// - `is_negated` is true if the `!T in` format was found instead of `T in` (when `is_conditional` is true)
fn parse_parameters(input: ParseStream, is_conditional: bool) -> syn::parse::Result<(ArgType, Vec<Type>, bool)> {
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
            let inner_vars: ParseStream = &content.into();
            Punctuated::<Type, Token![,]>::parse_terminated(&inner_vars)?
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
        let (args, types, _) = parse_parameters(input, false)?;
        Ok(TraitGen { args, types })
    }
}

/// Attribute argument parser used for the inner conditional attributes
impl Parse for CondParams {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let (args, types, is_negated) = parse_parameters(input, true)?;
        let generic_arg = if let ArgType::Cond(t) = args { t } else { panic!("can't happen") };
        Ok(CondParams {
            generic_arg,
            types: types.into_iter().collect(),
            is_negated,
        })
    }
}

//==============================================================================
// Procedural macros

fn substitute(item: TokenStream, mut types: Subst) -> TokenStream {
    if VERBOSE || VERBOSE_TF {
        println!("{}\ntrait_gen for {} -> {}: {}",
                 "=".repeat(80),
                 pathname(&types.generic_arg),
                 if types.is_path { "PATH" } else { "TYPE" },
                 &types.types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", ")
        )
    }
    if VERBOSE || VERBOSE_TF { println!("\n{}\n{}", item, "-".repeat(80)); }
    let mut output = TokenStream::new();
    let ast: File = syn::parse(item).unwrap();
    while !types.types.is_empty() {
        let mut modified_ast = ast.clone();
        types.visit_file_mut(&mut modified_ast);
        output.extend(TokenStream::from(quote!(#modified_ast)));
        assert!(types.can_subst_path.is_empty(), "self.enabled has {} entries after type {}",
                types.can_subst_path.len(), pathname(types.types.first().unwrap()));
        types.types.remove(0);
    }
    if VERBOSE { println!("end trait_gen for {}\n{}", pathname(&types.generic_arg), "-".repeat(80)); }
    output
}

/// Generates the attached implementation code for all the types given in argument.
///
/// The attribute is placed before the pseudo-generic code to implement. The _generic arguments_
/// are given first, followed by a right arrow (`->`) and a list of types that will replace the
/// argument in the generated implementations:
///
/// ```rust
/// # use trait_gen::trait_gen;
/// # struct Type1; struct Type2; struct Type3;
/// # trait Trait {}
/// #[trait_gen(T -> Type1, Type2, Type3)]
/// impl Trait for T {
///     // ...
/// }
/// ```
///
/// The attribute macro successively substitutes the generic argument `T` in the code with
/// the given types (`Type1`, `Type2`, `Type3`) to generate each implementation.
///
/// All the [type paths](https://doc.rust-lang.org/reference/paths.html#paths-in-types) beginning
/// with `T` in the code have that part replaced. For example, `T::default()` generates
/// `Type1::default()`, `Type2::default()` and so on, but `super::T` is unchanged. Similarly, all
/// the [types](https://doc.rust-lang.org/reference/types.html) including `T` in the code have that
/// part replaced; for example, `&T` or `Box<T>`.
///
/// The compiler will trigger an error if the resulting code is wrong. For example
/// `#[trait_gen(T -> u64, f64)]` cannot be applied to `let x: T = 0;` because `0` is not a valid
/// floating-point literal.
///
/// Finally, the actual type of `T` replaces any occurrence of `${T}` in doc comments, macros, and
/// string literals.
///
/// _Notes:_
/// - _Using the letter "T" is not mandatory; any type path will do. For example, `g::Type` is fine
/// too. But to make it easy to read and similar to a generic implementation, short upper-case identifiers
/// are preferred._
/// - _If a `<..>` is required in the generic argument, the
/// [turbofish syntax](https://doc.rust-lang.org/reference/paths.html#r-paths.expr.turbofish) must be used.
/// For example, use `T::<U>` and not `T<U>`._
/// - _`type_gen` is a synonym attribute that can be used instead of `trait_gen`. This can be disabled with
/// the `no_type_gen` feature, in case it conflicts with another 3rd-party attribute._
///
/// See the [crate documentation](crate) for more details.
///
/// ## Example
///
/// ```rust
/// # use trait_gen::trait_gen;
/// # trait MyLog { fn my_log2(self) -> u32; }
/// #[trait_gen(T -> u8, u16, u32, u64, u128)]
/// impl MyLog for T {
///     /// Logarithm base 2 for `${T}`
///     fn my_log2(self) -> u32 {
///         T::BITS - 1 - self.leading_zeros()
///     }
/// }
///
/// #[trait_gen(T -> u8, u16, u32, u64, u128)]
/// #[trait_gen(U -> &T, &mut T, Box<T>)]
/// impl MyLog for U {
///     /// Logarithm base 2 for `${U}`
///     fn my_log2(self) -> u32 {
///         MyLog::my_log2(*self)
///     }
/// }
/// ```
#[proc_macro_attribute]
#[proc_macro_error]
pub fn trait_gen(args: TokenStream, item: TokenStream) -> TokenStream {
    let mut attribute = match syn::parse::<TraitGen>(args) {
        Ok(types) => types,
        Err(err) => abort!(err.span(), err;
            help = "The expected format is: #[trait_gen(T -> Type1, Type2, Type3)]"),
    };
    let mut output = TokenStream::new();
    let args = std::mem::replace(&mut attribute.args, ArgType::None);
    match &args {
        ArgType::Tuple(paths) => {
            // generates all the permutations
            let mut subst = Subst::from_trait_gen(attribute.clone(), paths[0].clone());
            let types = std::mem::take(&mut subst.types);
            let new_iterators = (0..paths.len()).map(|_| types.iter()).collect::<Vec<_>>();
            let mut values = vec![];
            let mut iterators = vec![];
            loop {
                // fill missing iterators with fresh ones:
                for mut new_iter in new_iterators.iter().skip(iterators.len()).cloned() {
                    values.push(new_iter.next().unwrap());
                    iterators.push(new_iter);
                }
                // do the substitutions:
                let mut stream = item.clone();
                for (arg, &ty) in paths.iter().zip(values.iter()) {
                    subst.generic_arg = arg.clone();
                    subst.types = vec![ty.clone()];
                    stream = substitute(stream, subst.clone());
                }
                output.extend(stream);
                // pops dead iterators and increases the next one:
                while let Some(mut it) = iterators.pop() {
                    values.pop();
                    if let Some(v) = it.next() {
                        values.push(v);
                        iterators.push(it);
                        break;
                    }
                }
                if values.is_empty() { break }
            }
        }
        ArgType::Permutation(path1, path2) | ArgType::StrictOrder(path1, path2) | ArgType::NonStrictOrder(path1, path2) => {
            // we could translate the attribute into simple attributes using conditionals, but it's
            // easier, lighter, and safer to simply generate and filter the combinations
            let (_, types) = to_subst_types(attribute.types.clone());
            let mut subst = Subst::from_trait_gen(attribute.clone(), path1.clone());
            for (i1, p1) in types.iter().enumerate() {
                for (i2, p2) in types.iter().enumerate() {
                    let cond = match &args {
                        ArgType::Permutation(_, _) => i1 != i2,
                        ArgType::StrictOrder(_, _) => i1 < i2,
                        ArgType::NonStrictOrder(_, _) => i1 <= i2,
                        _ => panic!("can't happen")
                    };
                    if cond {
                        subst.types = vec![p1.clone()];
                        subst.generic_arg = path1.clone();
                        let stream = substitute(item.clone(), subst.clone());
                        subst.types = vec![p2.clone()];
                        subst.generic_arg = path2.clone();
                        output.extend(substitute(stream, subst.clone()));
                    }
                }
            }
        }
        _ => panic!("can't happen"),
    }
    if VERBOSE { println!("{}\n{}", output, "=".repeat(80)); }
    output
}

#[cfg(not(feature = "no_type_gen"))]
/// Generates the attached code for all the types given in argument.
///
/// This is only a synonym of the [trait_gen()] attribute, and it's provided since these attributes can
/// be applied to other elements than trait implementations.
#[proc_macro_attribute]
#[proc_macro_error]
pub fn type_gen(args: TokenStream, item: TokenStream) -> TokenStream {
    trait_gen(args, item)
}

//==============================================================================
// Conditional attributes

fn process_conditional_attribute(name: &str, args: TokenStream, item: TokenStream) -> TokenStream {
    if VERBOSE { println!("process_conditional_attribute({}, {})", args.to_string(), item.to_string()); }
    let new_code = match syn::parse::<CondParams>(args) {
        Ok(attr) => {
            if attr.types.contains(&attr.generic_arg) ^ attr.is_negated {
                item                // enables the code
            } else {
                TokenStream::new()  // disables the code
            }
        }
        Err(err) => {
            // shouldn't happen, unless the attribute is used out of a #[trait_gen] attribute scope
            abort!(err.span(), err;
            help = "The expected format is: #[{}(T in Type1, Type2, Type3)]", name);
        }
    };
    new_code
}

/// Generates the attached code if the condition is met.
///
/// Please refer to the [crate documentation](crate#conditional-code).
#[proc_macro_attribute]
#[proc_macro_error]
pub fn trait_gen_if(args: TokenStream, item: TokenStream) -> TokenStream {
    process_conditional_attribute("trait_gen_if", args, item)
}

#[cfg(not(feature = "no_type_gen"))]
/// Generates the attached code if the condition is met.
///
/// This is only a synonym of the [trait_gen_if()] attribute, and it's provided since these attributes can
/// be applied to other elements than trait implementations.
///
/// Please refer to the [crate documentation](crate#conditional-code).
#[proc_macro_attribute]
#[proc_macro_error]
pub fn type_gen_if(args: TokenStream, item: TokenStream) -> TokenStream {
    process_conditional_attribute("type_gen_if", args, item)
}
