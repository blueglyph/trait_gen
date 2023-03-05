// Copyright 2023 Redglyph
//
// Macros and helpers. Contains procedural macros so nothing else than macros can be exported.

//! # The trait_gen library
//!
//! This library provides attributes to generate the trait implementations for several
//! types, without the need for custom declarative macros.
//!
//! In the example below, the `Add` trait is implemented for `Meter`, `Foot` and `Mile`.
//! The `T` type identifier is used to mark where the substitution takes place; it can be an
//! existing type or alias but it's not mandatory.
//!
//! ```rust
//! # use std::ops::Add;
//! use trait_gen::trait_gen;
//!
//! pub struct Meter(f64);
//! pub struct Foot(f64);
//! pub struct Mile(f64);
//!
//! #[trait_gen(T -> Meter, Foot, Mile)]
//! impl Add for T {
//!     type Output = T;
//!
//!     fn add(self, rhs: T) -> Self::Output {
//!         Self(self.0 + rhs.0)
//!     }
//! }
//! ```
//!
//! The `trait_gen` attribute has the same effect as this custom declarative macro:
//!
//! ```rust
//! # use std::ops::Add;
//! # pub struct Meter(f64);
//! # pub struct Foot(f64);
//! # pub struct Mile(f64);
//! macro_rules! impl_add_length {
//!     ($($t:ty)*) => (
//!         $(impl Add for $t {
//!             type Output = $t;
//!
//!             fn add(self, rhs: $t) -> Self::Output {
//!                 Self(self.0 + rhs.0)
//!             }
//!         })*
//!     )
//! }
//!
//! impl_add_length! { Meter Foot Mile }
//! ```
//!
//! The advantages of the first method are the clarity of the native code, the support of
//! refactoring tools, editor syntactic and semantic awareness, and not having to convert the code into
//! a declarative macro. Looking for the definition of an implementation method is also much easier
//! with the full support of code-aware editors!
//!
//! The disadvantage is the current lack of support for procedural macros with the _IntelliJ_ plugin,
//! although this is an ongoing work (see
//! [tracking issue](https://github.com/intellij-rust/intellij-rust/issues/6908)). A few
//! work-arounds are discussed [later](#code-awareness-issues).
//!
//! There are also a few limitations of the current version described in the [Limitations](#limitations)
//! section.
//!
//! <br/>
//!
//! ## The trait_gen attribute
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # struct type1; struct type2; struct type3;
//! # trait Trait {}
//! #[trait_gen(T -> type1, type2, type3)]
//! impl Trait for T {
//!     // ...
//! }
//! ```
//! This attribute successively substitutes the `T` type parameter, which is used as a
//! type in the attached source code, with each of the following types (`type1`, `type2`, `type3`)
//! to generate all the implementations.
//!
//! All paths beginning with `T` in the code have this segment replaced. For example,
//! `T::default()` generates `type1::default()`, `type2::default()` and so on, but
//! `super::T` is unchanged.
//!
//! The code must of course be compatible with all the types, or the compiler will trigger the
//! relevant errors. For example `#[trait_gen(T -> u64, f64)]` cannot be used with `Self(0)` because
//! `0` is not a valid floating-point literal.
//!
//! The actual type name replaces any occurrence of the parameter with the `${T}` format in doc
//! comments, macros and string literals:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! trait Trait {
//!     fn text(&self) -> String;
//! }
//! #[trait_gen(T -> u32, u64)]
//! impl Trait for T {
//!     /// Produces a string representation for ${T}
//!     fn text(&self) -> String {
//!         let ty = "${T}".to_string();
//!         format!("{}: {}", ty, self)
//!     }
//! }
//!
//! assert_eq!(1_u32.text(), "u32: 1");
//! assert_eq!(2_u64.text(), "u64: 2");
//! ```
//!
//! <br/>
//!
//! ## Alternative format
//!
//! The attribute supports a shorter "legacy" format which was used in the earlier versions:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # struct type1; struct type2; struct type3;
//! # trait Trait {}
//! #[trait_gen(type1, type2, type3)]
//! impl Trait for type1 {
//!     // ...
//! }
//! ```
//!
//! Here, `type2` and `type3` are literally substituted for `type1` to generate their implementation,
//! then the original code is implemented for `type1`. This is a shortcut for the equivalent
//! attribute with the other format:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # struct type1; struct type2; struct type3;
//! # trait Trait {}
//! #[trait_gen(type1 -> type2, type3, type1)]
//! impl Trait for type1 {
//!     // ...
//! }
//! ```
//!
//! _Remark: this strange ordering comes from an optimization in the legacy format. This makes no
//! difference, except the order of the compiler messages if there are warnings or errors in the
//! code - that's the only reason we mention it here._
//!
//! The short format can be used when there is no risk of confusion, like in the example below.
//! All the `Meter` instances must change, it is unlikely to be mixed with `Foot` and `Mile`, so
//! using an alias is unnecessary. The type to replace in the code must be in first position in
//! the parameter list:
//!
//! ```rust
//! use std::ops::Add;
//! use trait_gen::trait_gen;
//!
//! pub struct Meter(f64);
//! pub struct Foot(f64);
//! pub struct Mile(f64);
//!
//! #[trait_gen(Meter, Foot, Mile)]
//! impl Add for Meter {
//!     type Output = Meter;
//!
//!     fn add(self, rhs: Meter) -> Self::Output {
//!         Self(self.0 + rhs.0)
//!     }
//! }
//! ```
//!
//! In some situations, one of the implemented types happens to be required in all the
//! implementations. Consider the following example, in which the return type is always `u64`:
//!
//! ```rust,compile_fail
//! # use trait_gen::trait_gen;
//! pub trait ToU64 {
//!     fn into_u64(self) -> u64;
//! }
//!
//! #[trait_gen(u64, i64, u32, i32, u16, i16, u8, i8)]
//! impl ToU64 for u64 {
//!     fn into_u64(self) -> u64 {  // ERROR! Replaced by -> i64, u32, ...
//!         self as u64
//!     }
//! }
//! ```
//!
//! This doesn't work because the return type of `into_u64()` will be replaced too! To prevent it,
//! an alias must be used (or the other attribute format). This works:
//!
//! ```rust
//! # use trait_gen::trait_gen;
//! # pub trait ToU64 {
//! #     fn into_u64(self) -> u64;
//! # }
//! #
//! type T = u64;
//!
//! #[trait_gen(T, i64, u32, i32, u16, i16, u8, i8)]
//! impl ToU64 for T {
//!     fn into_u64(self) -> u64 {
//!         self as u64
//!     }
//! }
//! ```
//!
//! <br/>
//!
//! ## Code awareness issues
//!
//! _rust-analyzer_ supports procedural macros for code awareness, so everything should be fine for
//! editors based on this Language Server Protocol implementation. Unfortunately this isn't the
//! case of all IDEs yet, which removes some benefits of using this macro. For instance, the
//! _IntelliJ_ plugin is not able to provide much support while typing the code for an unknown
//! `T` type, nor can it find the definition of the implemented methods, or even
//! suggest them.
//!
//! Here are two work-arounds that help when typing the trait implementation. However, they can't
//! do much about code awareness when the trait methods are used later. Hopefully the remaining
//! IDEs will provide more support for procedural macros soon.
//!
//! * Defining a type alias for the identifier used in the attribute doesn't change the produced
//! code, but it allows the editor to understand it without expanding the macro:
//!
//!   ```rust
//!     # use trait_gen::trait_gen;
//!     pub trait ToU64 {
//!         fn into_u64(self) -> u64;
//!     }
//!
//!     type T = u64;
//!
//!     #[trait_gen(T -> u64, i64, u32, i32, u16, i16, u8, i8)]
//!     impl ToU64 for T {
//!         fn into_u64(self) -> u64 {
//!             self as u64
//!         }
//!     }
//!   ```
//!
//! * Implementing for an existing type then using it as the type parameter is another possibility,
//! but it may look more confusing so use it with caution:
//!
//!   ```rust
//!     # use trait_gen::trait_gen;
//!     pub trait AddMod {
//!         fn add_mod(self, other: Self, m: Self) -> Self;
//!     }
//!
//!     // No need to use `type T = u32` in such a simple case:
//!     #[trait_gen(u32 -> u32, i32, u64, i64, f32, f64)]
//!     impl AddMod for u32 {
//!         fn add_mod(self, other: Self, m: Self) -> Self {
//!             (self + other) % m
//!         }
//!     }
//!   ```
//!
//! <br/>
//!
//! ## Limitations
//!
//! * Rust doesn't allow alias constructors with the "legacy" format. `Self` or a trait associated
//! type is usually equivalent - here, `Self(1.0)`. If there is no alternative, consider using
//! the `Default` trait or creating a specific one.
//!
//!   ```rust,compile_fail
//!   # use trait_gen::trait_gen;
//!   # trait Neutral { fn mul_neutral(&self) -> Self; }
//!   # struct Foot(f64);
//!   # struct Mile(f64);
//!   # struct Meter(f64);
//!   type T = Meter;
//!
//!   #[trait_gen(T, Foot, Mile)]
//!   impl Neutral for T {
//!       fn mul_neutral(&self) -> Self {
//!           T(1.0)  // <== ERROR, use Self(1.0) instead
//!       }
//!   }
//!   ```
//!
//!   The other attribute format allows the substitution:
//!
//!   ```rust
//!   # use trait_gen::trait_gen;
//!   # trait Neutral { fn mul_neutral(&self) -> Self; }
//!   # struct Foot(f64);
//!   # struct Mile(f64);
//!   # struct Meter(f64);
//!   #[trait_gen(T -> Meter, Foot, Mile)]
//!   impl Neutral for T {
//!       fn mul_neutral(&self) -> Self {
//!           T(1.0)  // <== always substituted with either Meter, Foot or Mile
//!       }
//!   }
//!   ```
//!
//! * The attribute doesn't handle scopes, so it doesn't support any type declaration with the same name
//! as the type that must be substituted, including generics. This, for instance, fails to compile:
//!
//!   ```rust,compile_fail
//!   use num::Num;
//!   use trait_gen::trait_gen;
//!
//!   trait AddMod {
//!       type Output;
//!       fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output;
//!   }
//!
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
//! * Substitutions are limited to single segments, like `Meter`. They don't support multiple
//! segments or arguments, like `super::Meter` or `Meter<f64>`. The same applies to the attribute
//! parameter: `T -> ...` is allowed, but not `super::T -> ...`. This can be worked around by
//! using a type alias or a `use` clause.

use proc_macro::TokenStream;
use std::fmt::{Display, Formatter};
use proc_macro_error::{proc_macro_error, abort};
use quote::{quote, ToTokens};
use syn::{Generics, GenericParam, Token, parse_macro_input, File, TypePath, Path, PathArguments, Expr, Lit, LitStr, ExprLit, Macro, parse_str, Attribute, PathSegment, GenericArgument};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Colon2;
use syn::visit_mut::VisitMut;

const VERBOSE: bool = false;

#[derive(Debug)]
struct Types {
    current_type: Path,
    new_types: Vec<Path>,
    current_defined: bool,
    enabled: Vec<bool> // cannot substitue when last is false (can substitute if empty)
}

impl Types {
    fn substitution_enabled(&self) -> bool {
        *self.enabled.last().unwrap_or(&true)
    }
}

impl Display for Types {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "PathTypes {{\n  current_types: {}\n  new_types: {}\n  current_defined: {}\n  enabled:  {}\n}}",
            pathname(&self.current_type),
            self.new_types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", "),
            self.current_defined.to_string(),
            self.enabled.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ")
        )
    }
}

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
}

trait NodeMatch {
    fn match_prefix(&self, other: &Self) -> bool;
}

impl NodeMatch for GenericArgument {
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

impl VisitMut for Types {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        let mut enabled = self.substitution_enabled();
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
        self.enabled.push(enabled);
        syn::visit_mut::visit_expr_mut(self, node);
        self.enabled.pop();
    }

    fn visit_generics_mut(&mut self, i: &mut Generics) {
        if let Some(segment) = self.current_type.segments.first() {
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

    fn visit_expr_lit_mut(&mut self, node: &mut ExprLit) {
        if let Lit::Str(lit) = &node.lit {
            // substitutes "${T}" in expression literals (not used in macros, see visit_macro_mut)
            if let Some(ts_str) = replace_str(
                &lit.to_token_stream().to_string(),
                &format!("${{{}}}", pathname(&self.current_type)),
                &pathname(self.new_types.first().unwrap()))
            {
                let new_lit: LitStr = parse_str(&ts_str).expect(&format!("parsing LitStr failed: {}", ts_str));
                node.lit = Lit::Str(new_lit);
            } else {
                syn::visit_mut::visit_expr_lit_mut(self, node);
            }
        }
    }

    fn visit_path_mut(&mut self, path: &mut Path) {
        if self.substitution_enabled() {
            let pathname = pathname(path);
            if let Some(length) = path_prefix_len(&self.current_type, path) {
                if VERBOSE { println!("path: {} length = {}", pathname, length); }
                for (seg, new_seg) in path.segments.iter_mut().zip(&self.new_types.first().unwrap().segments) {
                    // if VERBOSE { println!("- {:?} -> {:?}", seg, new_seg); }
                    seg.ident = new_seg.ident.clone();
                    if !new_seg.arguments.is_empty() {
                        seg.arguments = new_seg.arguments.clone();
                    }
                }
            } else {
                if VERBOSE { println!("path: {} mismatch", pathname); }
            }
        } else {
            if VERBOSE { println!("disabled path: {}", pathname(path)); }
        }
        syn::visit_mut::visit_path_mut(self, path);
    }

    fn visit_type_path_mut(&mut self, typepath: &mut TypePath) {
        self.enabled.push(true);
        let TypePath { path, .. } = typepath;
        if VERBOSE { println!("typepath: {}", pathname(path)); }
        syn::visit_mut::visit_type_path_mut(self, typepath);
        self.enabled.pop();
    }

    fn visit_macro_mut(&mut self, node: &mut Macro) {
        // substitutes "${T}" in macros
        if let Some(ts_str) = replace_str(
            &node.tokens.to_string(),
            &format!("${{{}}}", pathname(&self.current_type)),
            &pathname(self.new_types.first().unwrap()))
        {
            let new_ts: proc_macro2::TokenStream = ts_str.parse().expect(&format!("parsing Macro failed: {}", ts_str));
            node.tokens = new_ts;
        } else {
            syn::visit_mut::visit_macro_mut(self, node);
        }
    }

    fn visit_attribute_mut(&mut self, node: &mut Attribute) {
        if let Some(PathSegment { ident, .. }) = node.path.segments.first() {
            if ident.to_string() == "doc" {
                if let Some(ts_str) = replace_str(
                    &node.tokens.to_string(),
                    &format!("${{{}}}", pathname(&self.current_type)),
                    &pathname(self.new_types.first().unwrap()))
                {
                    let new_ts: proc_macro2::TokenStream = ts_str.parse().expect(&format!("parsing attribute failed: {}", ts_str));
                    node.tokens = new_ts;
                }
                return
            }
        }
        syn::visit_mut::visit_attribute_mut(self, node);
    }
}

/// Attribute argument parser
impl Parse for Types {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let first = input.parse::<Path>()?;
        if input.peek(Token![->]) {
            let current_type = first;
            input.parse::<Token![->]>()?;
            let vars = Punctuated::<Path, Token![,]>::parse_terminated(input)?;
            let new_types: Vec<Path> = vars.into_iter().collect();
            Ok(Types { current_type, new_types, current_defined: false, enabled: Vec::new() })
        } else {
            input.parse::<Token![,]>()?;
            let vars = Punctuated::<Path, Token![,]>::parse_terminated(input)?;
            let new_types: Vec<Path> = vars.into_iter().collect();
            let current_type = first;
            Ok(Types { current_type, new_types, current_defined: true, enabled: Vec::new() })
        }
    }
}

fn set_tubofish(path: &mut Path) {
    for segment in &mut path.segments {
        if let PathArguments::AngleBracketed(generic_args) = &mut segment.arguments {
            generic_args.colon2_token = Some(Colon2::default());
        }
    }
}

/// Generates the attached trait implementation for all the types given in parameter.
///
/// In the example below, the `Add` trait is implemented for `Meter`, `Foot` and `Mile`. The
/// `T` type identifier is used to mark where the substitution takes place; it can be an existing type
/// or alias but it's not mandatory.
///
/// ```rust
/// # use std::ops::Add;
/// use trait_gen::trait_gen;
///
/// pub struct Meter(f64);
/// pub struct Foot(f64);
/// pub struct Mile(f64);
///
/// #[trait_gen(T -> Meter, Foot, Mile)]
/// impl Add for T {
///     type Output = T;
///
///     fn add(self, rhs: T) -> Self::Output {
///         T(self.0 + rhs.0)
///     }
/// }
/// ```
///
/// <br/>
///
/// ## Alternative format
///
/// The short format can be used when there is no risk of confusion, like in the example below.
/// All the `Meter` instances must change, it is unlikely to be mixed with `Foot` and `Mile`, so
/// using an alias is unnecessary. The type to replace in the code must be in first position in
/// the parameter list:
///
/// ```rust
/// use std::ops::Add;
/// use trait_gen::trait_gen;
///
/// pub struct Meter(f64);
/// pub struct Foot(f64);
/// pub struct Mile(f64);
///
/// #[trait_gen(Meter, Foot, Mile)]
/// impl Add for Meter {
///     type Output = Meter;
///
///     fn add(self, rhs: Meter) -> Self::Output {
///         Self(self.0 + rhs.0)
///     }
/// }
/// ```
///
/// This is a shortcut for the other attribute format `#[trait_gen(Meter -> Meter, Foot, Mile)]`.
/// The type to replace must come first in the attribute parameter list - here, `Meter`.
///
/// <br/>
///
/// ## Limitations
///
/// * Rust doesn't allow alias constructors with the "legacy" format. `Self` or a trait associated
/// type is usually equivalent - here, `Self(1.0)`. If there is no alternative, consider using
/// the `Default` trait or creating a specific one.
///
///   ```rust,compile_fail
///   # use trait_gen::trait_gen;
///   # trait Neutral { fn mul_neutral(&self) -> Self; }
///   # struct Foot(f64);
///   # struct Mile(f64);
///   # struct Meter(f64);
///   #[trait_gen(T, Foot, Mile)]
///   impl Neutral for T {
///       fn mul_neutral(&self) -> Self {
///           T(1.0)  // <== ERROR, use Self(1.0) instead
///       }
///   }
///   ```
///
///   The other attribute format allows the substitution:
///
///   ```rust,compile_fail
///   #[trait_gen(T -> Meter, Foot, Mile)]
///   impl Neutral for T {
///       fn mul_neutral(&self) -> Self {
///           T(1.0)  // <== replaced
///       }
///   }
///   ```
///
/// * The macro doesn't handle scopes, so it doesn't support any type declaration with the same name
/// as the type that must be substituted, including generics. This, for instance, fails to compile:
///
///   ```rust,compile_fail
///   #[trait_gen(T -> u64, i64, u32, i32)]
///   impl AddMod for T {
///       type Output = T;
///
///       fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output {
///           fn int_mod<T: Num> (a: T, m: T) -> T { // <== ERROR, conflicting 'T'
///               a % m
///           }
///           int_mod(self + rhs, modulo)
///       }
///   }
///   ```
///
/// * Substitutions are limited to single segments, like `Meter`. They don't support multiple
/// segments or arguments, like `super::Meter` or `Meter<f64>`. The same applies to the attribute
/// parameter: `T -> ...` is allowed, but not `super::T -> ...`. This can be worked around by
/// using a type alias or a `use` clause.
#[proc_macro_attribute]
#[proc_macro_error]
pub fn trait_gen(args: TokenStream, item: TokenStream) -> TokenStream {
    let mut types = parse_macro_input!(args as Types);
    for ty in types.new_types.iter_mut() {
        // the turbofish is necessary in expressions, and not an error elsewhere, we simplify
        // by setting the turbofish in all replacements:
        set_tubofish(ty);
    }
    if VERBOSE { println!("{}\ntrait_gen for {} -> {}",
                          "=".repeat(80),
                          pathname(&types.current_type),
                          &types.new_types.iter().map(|t| pathname(t)).collect::<Vec<_>>().join(", ")
                 )}
    if VERBOSE { println!("\n{}\n{}", item, "-".repeat(80)); }
    let ast: File = syn::parse(item).unwrap();
    let mut output = TokenStream::new();
    while !types.new_types.is_empty() {
        let mut modified_ast = ast.clone();
        types.visit_file_mut(&mut modified_ast);
        output.extend(TokenStream::from(quote!(#modified_ast)));
        assert!(types.enabled.is_empty(), "self.enabled has {} entries after type {}",
                types.enabled.len(), pathname(types.new_types.first().unwrap()));
        types.new_types.remove(0);
    }
    if types.current_defined {
        output.extend(TokenStream::from(quote!(#ast)));
    }
    if VERBOSE { println!("end trait_gen for {}\n{}", pathname(&types.current_type), "-".repeat(80)); }
    if VERBOSE { println!("{}\n{}", output, "=".repeat(80)); }
    output
}
