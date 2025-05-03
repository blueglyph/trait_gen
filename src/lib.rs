// Copyright 2023 Redglyph
//
// Macros and helpers. Contains procedural macros so nothing else than macros can be exported.

//! # The trait_gen library
//!
//! This library provides an attribute macro to generate the implementations for several
//! types without needing custom declarative macros, code repetition, or blanket implementations.
//! It makes the code easier to read and to maintain.
//!
//! It was first intended at trait implementation, hence the name of the crate, but it can also
//! be used on generic type implementations; there are some examples in the [integration tests](https://github.com/blueglyph/trait_gen/blob/v1.2.0/tests/integration.rs).
//!
//! Here is a short example:
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
//! impl MyLog for u16 {
//!     fn my_log2(self) -> u32 {
//!         u16::BITS - 1 - self.leading_zeros()
//!     }
//! }
//! // and so on for the remaining types
//! ```
//!
//! ## Usage
//!
//! The attribute is placed before the pseudo-generic implementation code. The _generic argument_
//! is given first, followed by a right arrow (`->`) and a list of type arguments.
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
//! the following types (`Type1`, `Type2`, `Type3`) to generate all the implementations.
//!
//! All the [type paths](https://doc.rust-lang.org/reference/paths.html#paths-in-types) beginning with `T`
//! in the code have this part replaced. For example, `T::default()` generates `Type1::default()`,
//! `Type2::default()` and so on, but `super::T` is unchanged because it belongs to another scope.
//!
//! The code must be compatible with all the types, or the compiler will trigger the relevant
//! errors. For example `#[trait_gen(T -> u64, f64)]` cannot be applied to `let x: T = 0;` because `0`
//! is not a valid floating-point literal.
//!
//! Finally, the actual type of `T` replaces any `${T}` occurrence in doc comments, macros, and string literals.
//!
//! _Notes:_
//! - _Using the letter "T" is not mandatory; any type path will do. For example, `g::Type` is fine
//! too. But to make it easy to read and similar to a generic implementation, short upper-case identifiers
//! are preferred._
//! - _Two or more attributes can be chained to generate all the combinations._
//! - _`trait_gen` isn't restricted to trait implementations: it can be used on type implementations too._
//! - _`type_gen` is a synonym attribute that can be used instead of `trait_gen` when the `type_gen` feature
//!   is enabled (it requires `use trait_gen::type_gen`)_.
//!
//! For more examples, look at the [README.md](https://github.com/blueglyph/trait_gen/blob/v1.2.0/README.md)
//! or the crate [integration tests](https://github.com/blueglyph/trait_gen/blob/v1.2.0/tests/integration.rs).
//!
//! ## Conditional Code
//!
//! The use of conditional inclusion of code offers more flexibility in the implementation. Within a trait-gen
//! implementation, the pseudo-attribute `#[trait_gen_if(T in Type1, Type2, Type3]` disables the attached
//! code if `T` isn't in the list of types.
//!
//! Here is an example:
//!
//! ```rust
//! # use trait_gen::{trait_gen, trait_gen_if};
//!
//! trait Binary {
//!     const DECIMAL_DIGITS: usize;
//!     const SIGN: bool = false;
//!     fn display_length() -> usize;
//!     fn try_neg(self) -> Option<Self> where Self: Sized { None }
//! }
//!
//! #[trait_gen(T -> i8, u8, i32, u32)]
//! impl Binary for T {
//!     #[trait_gen_if(T in i8, u8)]
//!     const DECIMAL_DIGITS: usize = 3;
//!     #[trait_gen_if(T in i32, u32)]
//!     const DECIMAL_DIGITS: usize = 10;
//!     #[trait_gen_if(T in i8, i32)]
//!     const SIGN: bool = true;
//!
//!     fn display_length() -> usize {
//!         Self::DECIMAL_DIGITS + if T::SIGN { 1 } else { 0 }
//!     }
//!
//!     #[trait_gen_if(T in i8, i32)]
//!     fn try_neg(self) -> Option<Self> {
//!         Some(-self)
//!     }
//! }
//! ```
//!
//! The arguments can be placed on either side of `in`, so you can also use it to compare
//! arguments, as shown below. Note the `!T in U`, which means the code is enabled when
//! `T` is *not* in the given list, so here when `T != U`.
//!
//! ```rust
//! use trait_gen::{trait_gen, trait_gen_if};
//!
//! trait TypeEq<U> {
//!     fn same_type(&self, other: &U) -> bool;
//! }
//!
//! #[trait_gen(T -> u8, u16, u32)]
//! #[trait_gen(U -> u8, u16, u32)]
//! impl TypeEq<U> for T {
//!     #[trait_gen_if(T in U)]
//!     fn same_type(&self, _other: &U) -> bool {
//!         true
//!     }
//!     #[trait_gen_if(!T in U)]
//!     fn same_type(&self, _other: &U) -> bool {
//!         false
//!     }
//! }
//! ```
//!
//! We've seen earlier that `type_gen` was a synonym of `trait_gen`. For the sake of coherency, a
//! `type_gen_if` is also provided as a synonym of `trait_gen_if`.
//!
//! ## Limitations
//!
//! * The procedural macro of the `trait_gen` attribute can't handle scopes, so it doesn't support any
//! type declaration with the same literal as the generic argument. For instance, this code fails to compile
//! because of the generic function:
//!
//!   ```rust, ignore
//!   # use num::Num;
//!   # use trait_gen::trait_gen;
//!   #
//!   # trait AddMod {
//!   #     type Output;
//!   #     fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output;
//!   # }
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
use std::fmt::{Display, Formatter};
use proc_macro::TokenStream;
use proc_macro_error::{proc_macro_error, abort};
use quote::{quote, ToTokens};
use syn::{Generics, GenericParam, Token, File, TypePath, Path, PathArguments, Expr, Lit, LitStr, ExprLit, Macro, parse_str, Attribute, PathSegment, GenericArgument, Type, Error, bracketed, MetaList, token};
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
const TYPE_GEN: &str = if cfg!(feature = "type_gen") { "type_gen" } else { TRAIT_GEN_IF };

// Attributes for conditional implementation.
// Note: when the feature "type_gen" is disabled, we avoid matching "type_gen_if" by
//       making both constants equal (those constants are used in a match statement).
const TRAIT_GEN_IF: &str = "trait_gen_if";
const TYPE_GEN_IF: &str = if cfg!(feature = "type_gen") { "type_gen_if" } else { TRAIT_GEN_IF };

//==============================================================================
// Main substitution types and their trait implementations

#[derive(PartialEq)]
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

impl std::fmt::Debug for SubstType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SubstType::Path(p) => write!(f, "Path({})", pathname(p)),
            SubstType::Type(t) => write!(f, "Type({})", pathname(t)),
        }
    }
}

#[derive(Debug, PartialEq)]
/// Attribute format used in the original source code.
enum AttributeFormat {
    Arrow,      // #[trait_gen(T -> T1, T2, T3)]    impl Trait for T {...}
    Legacy,     // #[trait_gen(T1, T2, T3)]         impl Trait for T1 {...}
    In          // #[trait_gen(T in [T1, T2, T3])]  impl Trait for T {...}
}

impl AttributeFormat {
    fn is_legacy(&self) -> bool {
        self == &AttributeFormat::Legacy
    }

    fn is_in(&self) -> bool {
        self == &AttributeFormat::In
    }
}

/// Advanced formats
enum ArgType {
    /// - `#[trait_gen_if(T in U)`
    Cond(Type),
    /// All combinations (can have more than 2 arguments)
    /// - `#[trait_gen(T -> u8, u16)]`
    ///
    ///   (T) = (u8), (u16)
    /// - `#[trait_gen(T, U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u8), (u8, u16), (u8, u32), (u16, u8), (u16, u16), (u16, u32) , ...
    ///
    All(Vec<Path>),
    /// All combinations of 2 different arguments
    ///
    /// - `#[trait_gen(T != U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u16), (u8, u32), (u16, u8), (u16, u32), (u32, u8), (u32, u16)
    Diff(Path, Path),
    /// All combinations of 2 arguments where 1st's items are exclusively earlier in the list than the 2nd's
    ///
    /// - `#[trait_gen(T !< U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u16), (u8, u32), (u16, u32)
    Exclusive(Path, Path),
    /// All combinations of 2 arguments where 1st's items are inclusively earlier in the list than the 2nd's
    ///
    /// - `#[trait_gen(T =< U -> u8, u16, u32)]`
    ///
    ///   (T, U) = (u8, u8), (u8, u16), (u8, u32), (u16, u16), (u16, u32), (u32, u32)
    Inclusive(Path, Path),
}

impl std::fmt::Debug for ArgType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ArgType::Cond(c) => write!(f, "Cond({})", pathname(c)),
            ArgType::All(a) => write!(f, "All({})", a.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", ")),
            ArgType::Diff(p1, p2) => write!(f, "Diff({}, {})", pathname(p1), pathname(p2)),
            ArgType::Exclusive(p1, p2) => write!(f, "Exclusive({}, {})", pathname(p1), pathname(p2)),
            ArgType::Inclusive(p1, p2) => write!(f, "Inclusive({}, {})", pathname(p1), pathname(p2)),
        }
    }
}

#[derive(Debug)]
/// Attribute substitution data used to replace the generic argument in `generic_arg` with the
/// types in `new_types`.
struct Subst {
    /// generic argument to replace
    generic_arg: Path,
    /// types that replace the generic argument
    new_types: Vec<SubstType>,
    /// format
    format: AttributeFormat,
    /// Path substitution items if true, Type items if false
    is_path: bool,
    /// Context stack, cannot substitue paths when last is false (can substitute if empty)
    can_subst_path: Vec<bool>,
}

#[derive(Debug)]
/// Attribute data used to substitute arguments in inner `trait_gen`/`type_gen` attributes
struct AttrParams {
    /// generic argument to replace
    generic_arg: Path,
    /// types that replace the generic argument
    new_types: Vec<Type>,
    /// format
    format: AttributeFormat,
}

#[derive(Debug)]
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
    fn can_subst_path(&self) -> bool {
        *self.can_subst_path.last().unwrap_or(&true)
    }

    /// Gives a helpful list of type names that might be used in a substitution list.
    fn get_example_types(&self) -> String {
        // This is called for error messages, which happen only during the first visit_mut pass over
        // the inner attributes: we know that Subst still has all the types in `self.new_types`.
        let mut examples = self.new_types.iter().map(|t| pathname(t)).take(3).collect::<Vec<_>>();
        while examples.len() < 3 {
            examples.push(format!("Type{}", examples.len() + 1));
        }
        examples.join(", ")
    }
}

impl Display for Subst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "PathTypes {{\n  current_type: {}\n  new_types: {}\n  format: {:?}\n  enabled:  {}\n}}",
               pathname(&self.generic_arg),
               self.new_types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", "),
               self.format,
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

//==============================================================================
// Main substitution code

impl VisitMut for Subst {
    fn visit_attribute_mut(&mut self, node: &mut Attribute) {
        if let Some(PathSegment { ident, .. }) = node.path().segments.first() {
            let ident = ident.to_string();
            match ident.as_str() {
                // conditional pseudo-attribute (TYPE_GEN_IF == TRAIT_GEN_IF when type_gen is disabled)
                TRAIT_GEN_IF | TYPE_GEN_IF => {
                    // checks that the syntax is fine and performs the type substitutions if required
                    match node.parse_args::<CondParams>() {
                        Ok(cond) => {
                            let mut output = proc_macro2::TokenStream::new();
                            if VERBOSE { println!("- {} -> {}", pathname(&self.generic_arg), pathname(self.new_types.first().unwrap())); }
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
                    match node.parse_args::<AttrParams>() {
                        Ok(mut types) => {
                            let mut output = proc_macro2::TokenStream::new();
                            // It would be nice to give a warning if the format of the attributes were different,
                            // once there is a way to generate custom warnings (an error for that seems too harsh).
                            if !types.format.is_legacy() {
                                let g = types.generic_arg;
                                output.extend(quote!(#g -> ));
                            }
                            let mut first = true;
                            for ty in &mut types.new_types {
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
                &pathname(self.new_types.first().unwrap()))
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
            &pathname(self.new_types.first().unwrap()))
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
                match self.new_types.first().unwrap() {
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
                        // abort!(ty.span(), "Path '{}' cannot be substituted by type '{}'", path_name, pathname(ty));
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
                        if length < path_length || self.can_subst_path() {
                            // TODO: find a case where length < path_length
                            if VERBOSE { print!("[type] type path: {} length = {length}, path length = {path_length} {} -> ", path_name, if self.can_subst_path() { ", can_subst" } else { "" }); }
                            *node = if let SubstType::Type(ty) = self.new_types.first().unwrap() {
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
/// There are three syntax formats:
/// - `T -> Type1, Type2, Type3`
/// - `T in [Type1, Type2, Type3]` or `T in Type1, Type2, Type3`  (when `in_format_allowed` is true)
/// - `Type1, Type2, Type3` (legacy format)
///
/// The `is_conditional` parameter forces the "in" format and allows a negation, "!in". It also returns
/// a `Type` argument (`SubstType::Type`) instead of a `Path` because the argument will be substituted
/// by a type by the trait-gen attribute.
///
/// Returns (path, types, format, is_negated), where
/// - `path` is the generic argument `T` (or `Type1` in legacy format)
/// - `types` is a vector of parsed `Type` items: `Type1, Type2, Type3` (or `Type2, Type3` in legacy)
/// - `format` is the attribute format: arrow, legacy, or in
/// - `is_negated` is true if the `!in` format was found instead of `in` in a conditional
///
/// Note: we don't include `Type1` in `types` for the legacy format because the original stream will be copied
/// in the generated code, so only the remaining types are required for the substitutions.
fn parse_parameters(input: ParseStream, is_conditional: bool)
    -> syn::parse::Result<(ArgType, Vec<Type>, AttributeFormat, bool)>
{
    let is_negated = is_conditional && input.peek(Token![!]) && input.parse::<Token![!]>().is_ok();
    let args = if is_conditional {
        ArgType::Cond(input.parse::<Type>()?)
    } else {
        // determines the format
        let path1 = input.parse::<Path>()?;
        if input.peek(Token![,]) && input.parse::<Token![,]>().is_ok() {
            let mut list_args = vec![path1];
            loop {
                let p = input.parse::<Path>()?;
                list_args.push(p);
                if input.peek(Token![,]) {
                    _ = input.parse::<Token![,]>();
                } else {
                    break;
                }
            }
            ArgType::All(list_args)
        } else if input.peek(Token![!]) && input.parse::<Token![!]>().is_ok() {
            if input.peek(Token![=]) && input.parse::<Token![=]>().is_ok() {
                ArgType::Diff(path1, input.parse::<Path>()?)
            } else {
                input.parse::<Token![<]>()?;
                ArgType::Exclusive(path1, input.parse::<Path>()?)
            }
        } else {
            if input.peek(Token![=]) && input.parse::<Token![=]>().is_ok() {
                input.parse::<Token![<]>()?;
                ArgType::Inclusive(path1, input.parse::<Path>()?)
            } else {
                // that something else must be '->', so we return a single "normal" argument
                ArgType::All(vec![path1])
            }
        }
    };

    // note: legacy format not supported any more
    let format = if is_conditional && input.parse::<Token![in]>().and(Ok(true))? {
        AttributeFormat::In
    } else {
        input.parse::<Token![->]>()?;                           // "T -> Type1, Type2, Type3"
        AttributeFormat::Arrow
    };

    // collects the other arguments depending on format
    let types: Vec<Type>;
    let vars = match format {
        AttributeFormat::Legacy =>
            todo!("remove"),
        AttributeFormat::In => {
            // brackets are optional:
            if input.peek(token::Bracket) {
                let content;
                bracketed!(content in input);
                let inner_vars: ParseStream = &content.into();
                Punctuated::<Type, Token![,]>::parse_terminated(&inner_vars)?
            } else {
                Punctuated::<Type, Token![,]>::parse_terminated(input)?
            }
        }
        AttributeFormat::Arrow =>
            Punctuated::<Type, Token![,]>::parse_terminated(input)?,
    };
    types = vars.into_iter().collect();
    if types.is_empty() {
        return Err(Error::new(input.span(), "expected type"));
    }
    Ok((args, types, format, is_negated))
}

/// Attribute parser used for inner attributes
impl Parse for AttrParams {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let (args, types, format, _) = parse_parameters(&input, false)?;
        
        // FIXME: temporary
        let generic_arg = if let ArgType::All(mut v) = args { v.pop().unwrap() } else { panic!("not supported yet") };
        Ok(AttrParams { generic_arg, new_types: types, format })
    }
}

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

/// Attribute argument parser used for the inner conditional attributes
impl Parse for CondParams {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let (args, types, format, is_negated) = parse_parameters(input, true)?;
        assert!(format.is_in());
        let generic_arg = if let ArgType::Cond(t) = args { t } else { panic!("can't happen") };
        Ok(CondParams {
            generic_arg,
            types: types.into_iter().collect(),
            is_negated,
        })
    }
}

/// Attribute argument parser used for the procedural macro being processed
impl Parse for Subst {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let (args, types, format, _) = parse_parameters(input, false)?;
        
        // FIXME: temporary
        let generic_arg = if let ArgType::All(mut v) = args { v.pop().unwrap() } else { panic!("not supported yet: {args:?}") };
        let (is_path, new_types) = to_subst_types(types);
        Ok(Subst { generic_arg, new_types, format, is_path, can_subst_path: Vec::new() })
    }
}

//------------------------------------------------------------------------------

// This type is only used to implement the VisitMut trait.
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

/// Generates the attached implementation code for all the types given in argument.
///
/// The attribute is placed before the pseudo-generic implementation code. The _generic argument_
/// is given first, followed by a right arrow (`->`) and a list of type arguments.
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
/// the following types (`Type1`, `Type2`, `Type3`) to generate all the implementations.
///
/// All the [type paths](https://doc.rust-lang.org/reference/paths.html#paths-in-types) beginning with `T`
/// in the code have this part replaced. For example, `T::default()` generates `Type1::default()`,
/// `Type2::default()`, and so on, but `super::T` is unchanged because it belongs to another scope.
///
/// The code must be compatible with all the types, or the compiler will trigger the relevant
/// errors. For example, `#[trait_gen(T -> u64, f64)]` cannot be applied to `let x: T = 0;`, because `0`
/// is not a valid floating-point literal.
///
/// The `#[trait_gen_if(T in Type1, Type2, Type3)` can be used to conditionally enable the attached code
/// if `T` is included in the list of types, or to disable it when it's not included.
///
/// Finally, the actual type replaces any `${T}` occurrence in doc comments, macros and string literals.
///
/// _Notes:_
/// - _Using the letter "T" is not mandatory; any type path will do. For example, `g::Type` is fine
/// too. But to make it easy to read and similar to a generic implementation, short upper-case identifiers
/// are preferred._
/// - _Two or more attributes can be chained to generate all the combinations._
/// - _`trait_gen` can be used on type implementations too._
/// - _`type_gen` is a synonym attribute that can be used instead of `trait_gen` when the `type_gen` feature
///   is enabled (it requires `use trait_gen::type_gen`). Similarly, `type_gen_if` can be used instead of `trait_gen_if`_.
///
/// ## Examples
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
    let mut types = match syn::parse::<Subst>(args) {
        Ok(types) => types,
        Err(err) => {
            abort!(err.span(), err;
                help = "The expected format is: #[trait_gen(T -> Type1, Type2, Type3)]");
        }
    };
    if VERBOSE || VERBOSE_TF {
        println!("{}\ntrait_gen for {} -> {}: {}",
                 "=".repeat(80),
                 pathname(&types.generic_arg),
                 if types.is_path { "PATH" } else { "TYPE" },
                 &types.new_types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", ")
        )
    }
    if VERBOSE || VERBOSE_TF { println!("\n{}\n{}", item, "-".repeat(80)); }
    let mut output = match types.format {
        AttributeFormat::Arrow =>
            TokenStream::new(),
        AttributeFormat::Legacy =>
            item.clone(),
        AttributeFormat::In => {
            let message = format!(
                "Use of deprecated format '{} in [{}]' in #[trait_gen] macro",
                 pathname(&types.generic_arg),
                 &types.new_types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", "),
            );
            // no way to generate warnings in Rust
            if VERBOSE || VERBOSE_TF { println!("{}\nWARNING: \n{}", "=".repeat(80), message); }
            TokenStream::from(quote!(#[deprecated = #message]))
        }
    };
    let ast: File = syn::parse(item).unwrap();
    while !types.new_types.is_empty() {
        let mut modified_ast = ast.clone();
        types.visit_file_mut(&mut modified_ast);
        output.extend(TokenStream::from(quote!(#modified_ast)));
        assert!(types.can_subst_path.is_empty(), "self.enabled has {} entries after type {}",
                types.can_subst_path.len(), pathname(types.new_types.first().unwrap()));
        types.new_types.remove(0);
    }
    if VERBOSE { println!("end trait_gen for {}\n{}", pathname(&types.generic_arg), "-".repeat(80)); }
    if VERBOSE { println!("{}\n{}", output, "=".repeat(80)); }
    output
}

#[cfg(feature = "type_gen")]
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

#[cfg(feature = "type_gen")]
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
