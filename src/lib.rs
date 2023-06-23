// Copyright 2023 Redglyph
//
// Macros and helpers. Contains procedural macros so nothing else than macros can be exported.

//! # The trait_gen library
//!
//! This library provides an attribute macro to generate the trait implementations for several
//! types without needing custom declarative macros, code repetition, or blanket implementations.
//! It makes the code easier to read and to maintain.
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
//! Finally, the actual type replaces any `${T}` occurrence in doc comments, macros, and string literals.
//!
//! _Notes:_
//! - _Using the letter "T" is not mandatory; any type path will do. For example, `gen::Type` is fine
//! too. But to make it easy to read and similar to a generic implementation, short upper-case identifiers
//! are preferred._
//! - _Two or more attributes can be chained to generate all the combinations._
//! - _`trait_gen` can be used on type implementations too._
//!
//! For more examples, look at the [README.md](https://github.com/blueglyph/trait_gen/blob/v0.2.0/README.md)
//! or the crate [integration tests](https://github.com/blueglyph/trait_gen/blob/v0.2.0/tests/integration.rs).
//!
//! ## Legacy Format
//!
//! The attribute used a shorter format in earlier versions, which is still supported even though it
//! may be more confusing to read:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # struct Type1; struct Type2; struct Type3;
//! # trait Trait {}
//! #[trait_gen(Type1, Type2, Type3)]
//! impl Trait for Type1 {
//!     // ...
//! }
//! ```
//!
//! is a shortcut for the equivalent attribute with the other format:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # struct Type1; struct Type2; struct Type3;
//! # trait Trait {}
//! #[trait_gen(Type1 -> Type1, Type2, Type3)]
//! impl Trait for Type1 {
//!     // ...
//! }
//! ```
//!
//! ## Alternative Format
//!
//! An alternative format is also supported when the `in_format` feature is enabled:
//!
//! ```cargo
//! trait-gen = { version="0.3", features=["in_format"] }
//! ```
//!
//! **<u>Warning</u>: This feature is temporary, and there is no guarantee that it will be maintained.**
//!
//! Here, `in` is used instead of an arrow `->`, and the argument types must be between square brackets:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # trait MyLog { fn my_log2(self) -> u32; }
//! # #[cfg(feature = "in_format")]
//! #[trait_gen(T in [u8, u16, u32, u64, u128])]
//! # #[cfg(not(feature = "in_format"))]
//! # #[trait_gen(T -> u8, u16, u32, u64, u128)]
//! impl MyLog for T {
//!     fn my_log2(self) -> u32 {
//!         T::BITS - 1 - self.leading_zeros()
//!     }
//! }
//! ```
//!
//! Using this format issues 'deprecated' warnings that you can turn off by adding the `#![allow(deprecated)]`
//! directive at the top of the file or by adding `#[allow(deprecated)]` where the generated code is used.
//!
//! ## Limitations
//!
//! * The procedural macro of the `trait_gen` attribute can't handle scopes, so it doesn't support any
//! type declaration with the same literal as the generic argument. For instance, this code fails to compile
//! because of the generic function:
//!
//!   ```rust, compile_fail
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
//! it cannot be a more complex type like a reference or a slice. So you can use `gen::T<U> -> ...`
//! but not `&T -> ...`.

mod tests;

use proc_macro::TokenStream;
use std::fmt::{Display, Formatter};
use proc_macro_error::{proc_macro_error, abort};
use quote::{quote, ToTokens};
use syn::{Generics, GenericParam, Token, parse_macro_input, File, TypePath, Path, PathArguments, Expr, Lit, LitStr, ExprLit, Macro, parse_str, Attribute, PathSegment, GenericArgument, Type, parenthesized, parse2, Error, bracketed};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Colon2;
use syn::visit_mut::VisitMut;

const VERBOSE: bool = false;
const VERBOSE_TF: bool = false;

//==============================================================================
// Main substitution types and their trait implementations

#[derive(Debug)]
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

#[derive(Debug)]
/// Attribute substitution data used to replace the generic argument in `generic_arg` with the
/// types in `new_types`.
struct Subst {
    /// generic argument to replace
    generic_arg: Path,
    /// types that replace the generic argument
    new_types: Vec<SubstType>,
    /// legacy format if true
    legacy: bool,
    /// format `T in [...]` if true
    in_format: bool,
    /// Path substitution items if true, Type items if false
    is_path: bool,
    /// Context stack, cannot substitue paths when last is false (can substitute if empty)
    can_subst_path: Vec<bool>,
}

#[derive(Debug)]
/// Attribute data used to substitute arguments in inner `trait_gen` attributes
struct AttrParams {
    /// generic argument to replace
    generic_arg: Path,
    /// types that replace the generic argument
    new_types: Vec<Type>,
    /// legacy format if true
    legacy: bool,
}

impl Subst {
    fn can_subst_path(&self) -> bool {
        *self.can_subst_path.last().unwrap_or(&true)
    }
}

impl Display for Subst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "PathTypes {{\n  current_types: {}\n  new_types: {}\n  current_defined: {}\n  enabled:  {}\n}}",
               pathname(&self.generic_arg),
               self.new_types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", "),
               self.legacy.to_string(),
               self.can_subst_path.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ")
        )
    }
}

//==============================================================================
// Helper functions and traits

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
    // if VERBOSE { println!("- path_prefix_len(prefix: {}, full: {})", pathname(prefix), pathname(full_path)); }
    let prefix_len = prefix.segments.len();
    if full_path.leading_colon == prefix.leading_colon && full_path.segments.len() >= prefix_len {
        for (seg_full, seg_prefix) in full_path.segments.iter().zip(&prefix.segments) {
            if !seg_full.match_prefix(seg_prefix) {
                // if VERBOSE { print!("  - {:?} != {:?} ", pathname(seg_prefix), pathname(seg_full)); }
                return None;
            } else {
                // if VERBOSE { print!("  - {:?} ~= {:?} ", pathname(seg_prefix), pathname(seg_full)); }
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
        if let Some(PathSegment { ident, .. }) = node.path.segments.first() {
            match ident.to_string().as_str() {
                "doc" => {
                    if let Some(ts_str) = replace_str(
                        &node.tokens.to_string(),
                        &format!("${{{}}}", pathname(&self.generic_arg)),
                        &pathname(self.new_types.first().unwrap()))
                    {
                        let new_ts: proc_macro2::TokenStream = ts_str.parse().expect(&format!("parsing attribute failed: {}", ts_str));
                        node.tokens = new_ts;
                    }
                    return
                }
                "trait_gen" => {
                    if VERBOSE { println!("#trait_gen: '{}' in {}", pathname(&self.generic_arg), pathname(&node.tokens)); }
                    let new_args = process_attr_args(self, node.tokens.clone());
                    if VERBOSE { println!("=> #trait_gen: {}", pathname(&new_args)); }
                    node.tokens = new_args;
                    return
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
            Expr::Type(_) => enabled = true,

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
            // If U is both a constant and the generic argument, in an expression so when
            // self.substitution_enabled() == false, we must distinguish two cases:
            // - U::MAX must be replaced (length < path_length)
            // - U or U.add(1) must stay
            if length < path_length || self.can_subst_path() {
                if VERBOSE { print!("path: {} length = {}", path_name, length); }
                match self.new_types.first().unwrap() {
                    SubstType::Path(p) => {
                        let mut new_seg = p.segments.clone();
                        for seg in path.segments.iter().skip(length) {
                            new_seg.push(seg.clone());
                        }
                        // check if orphan arguments:
                        //     #[trait_gen(gen::T -> mod::Name, ...) { ... gen::T<'_> ... }
                        //     path     = gen :: T   <'_>    len = 2, subst enabled
                        //     new_path = mod :: Name        len = 2
                        //  => new_seg  = mod :: Name<'_>
                        let mut nth_new_seg = new_seg.last_mut().unwrap();
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
                            if VERBOSE { println!("type path: {} length = {}", path_name, length); }
                            *node = if let SubstType::Type(ty) = self.new_types.first().unwrap() {
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

/// Perform substitutions in the arguments of the inner attribute if necessary.
///
/// `
/// #[trait_gen(U -> i32, u32)]     // <== we are processing this attribute
/// #[trait_gen(T -> &U, &mut U)]   // <== change 'U' to 'i32' and 'u32'
/// impl Neg for T { /* .... */ }
/// `
fn process_attr_args(subst: &mut Subst, args: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    match parse2::<AttrParams>(args) {
        Ok(mut types) => {
            let mut output = proc_macro2::TokenStream::new();
            if !types.legacy {
                let gen = types.generic_arg;
                output.extend(quote!(#gen -> ));
            }
            let mut first = true;
            for ty in &mut types.new_types {
                if !first {
                    output.extend(quote!(, ));
                }
                // checks if substitutions must be made in that argument:
                subst.visit_type_mut(ty);

                output.extend(quote!(#ty));
                first = false;
            }

            // puts the parentheses back and returns the modified token stream
            proc_macro2::Group::new(proc_macro2::Delimiter::Parenthesis, output).into_token_stream()
        }
        Err(err) => {
            err.to_compile_error()
        }
    }
}

/// Parses the attribute arguments, and extracts the generic argument and the types that must substitute it.
///
/// There are three syntaxes:
/// - `T -> Type1, Type2, Type3`
/// - `T in [Type1, Type2, Type3]` (when "in_format" feature is enabled)
/// - `Type1, Type2, Type3` (legacy format)
///
/// Returns (path, types, legacy), where
/// - `path` is the generic argument `T` (or `Type1` in legacy format)
/// - `types` is a vector of parsed `Type` items: `Type1, Type2, Type3` (or `Type2, Type3` in legacy)
/// - `legacy` is true if the legacy format is used
/// - `in_format` is true if the `T in [Type1, Type2, Type3]` format is used
///
/// Note: we don't include `Type1` in `types` for the legacy format because the original stream will be copied
/// in the generated code, so only the remaining types are requires for the substitutions.
fn parse_parameters(input: ParseStream) -> syn::parse::Result<(Path, Vec<Type>, bool, bool)> {
    let current_type = input.parse::<Path>()?;
    let types: Vec<Type>;
    let arrow_format = input.peek(Token![->]);                  // "T -> Type1, Type2, Type3"
    let in_format = !arrow_format && input.peek(Token![in]);    // "T in [Type1, Type2, Type3]"
    let legacy = !arrow_format && !in_format;                   // "Type1, Type2, Type3"
    if legacy {
        input.parse::<Token![,]>()?;
        let vars = Punctuated::<Type, Token![,]>::parse_terminated(input)?;
        types = vars.into_iter().collect();
    } else {
        let vars = if cfg!(feature = "in_format") && in_format {
            input.parse::<Token![in]>()?;
            let content;
            bracketed!(content in input);
            Punctuated::<Type, Token![,]>::parse_terminated(&content.into())?
        } else {
            // removes the "->" and parses the arguments
            input.parse::<Token![->]>()?;
            Punctuated::<Type, Token![,]>::parse_terminated(input)?
        };
        types = vars.into_iter().collect();
        if types.is_empty() {
            return Err(Error::new(input.span(), "expected type"));
        }
    }
    Ok((current_type, types, legacy, in_format))
}

/// Attribute parser used for inner attributes
impl Parse for AttrParams {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        parenthesized!(content in input);
        let (current_type, types, legacy, _) = parse_parameters(&content.into())?;
        Ok(AttrParams { generic_arg: current_type, new_types: types, legacy })
    }
}

/// Attribute argument parser used for the procedural macro being processed
impl Parse for Subst {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let (current_type, mut types, legacy, in_format) = parse_parameters(input)?;
        let mut visitor = TurboFish;
        for ty in types.iter_mut() {
            visitor.visit_type_mut(ty);
        }
        let is_path = types.iter().all(|ty| matches!(ty, Type::Path(_)));
        let new_types = types.into_iter()
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
        Ok(Subst { generic_arg: current_type, new_types: new_types, legacy, in_format, is_path, can_subst_path: Vec::new() })
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
                generic_args.colon2_token = Some(Colon2::default());
            }
        }
    }
}

//==============================================================================

/// Generates the attached trait implementation for all the types given in argument.
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
/// Finally, the actual type replaces any `${T}` occurrence in doc comments, macros and string literals.
///
/// _Notes:_
/// - _Using the letter "T" is not mandatory; any type path will do. For example, `gen::Type` is fine
/// too. But to make it easy to read and similar to a generic implementation, short upper-case identifiers
/// are preferred._
/// - _Two or more attributes can be chained to generate all the combinations._
/// - _`trait_gen` can be used on type implementations too._
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
    let mut types = parse_macro_input!(args as Subst);
    let warning = if types.in_format {
        let message = format!(
            "Use of temporary format '{} in [{}]' in #[trait_gen] macro",
             pathname(&types.generic_arg),
             &types.new_types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", "),
        );
        // no way to generate warnings in Rust
        if VERBOSE || VERBOSE_TF { println!("{}\nWARNING: \n{}", "=".repeat(80), message); }
        Some(message)
    } else {
        None
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
    let ast: File = syn::parse(item).unwrap();
    let mut output = TokenStream::new();
    if let Some(message) = warning {
        output.extend(TokenStream::from(quote!(
            #[deprecated = #message]
        )));
    }
    while !types.new_types.is_empty() {
        let mut modified_ast = ast.clone();
        types.visit_file_mut(&mut modified_ast);
        output.extend(TokenStream::from(quote!(#modified_ast)));
        assert!(types.can_subst_path.is_empty(), "self.enabled has {} entries after type {}",
                types.can_subst_path.len(), pathname(types.new_types.first().unwrap()));
        types.new_types.remove(0);
    }
    if types.legacy {
        output.extend(TokenStream::from(quote!(#ast)));
    }
    if VERBOSE { println!("end trait_gen for {}\n{}", pathname(&types.generic_arg), "-".repeat(80)); }
    if VERBOSE { println!("{}\n{}", output, "=".repeat(80)); }
    output
}
