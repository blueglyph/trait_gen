// Copyright 2023 Redglyph
//
// Macros and helpers. Contains procedural macros so nothing else than macros can be exported.

//! # The trait_gen library
//!
//! This library provides attributes to generate the trait implementations for several
//! types, without the need for custom declarative macros.
//!
//! For example,
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
//! refactoring tools, editor syntactic awareness, and not having to convert the code to
//! the declarative macro syntax. Looking for the definition of an implementation method is
//! also much easier with the full support of code-aware editors!
//!
//! The disadvantage is the current lack of support for procedural macros with the IntelliJ plugin,
//! although this is an ongoing work (see
//! [tracking issue](https://github.com/intellij-rust/intellij-rust/issues/6908)). A few
//! work-arounds are discussed [later](#code-awareness-issues).
//!
//! There are also a few limitations of the current version described in the [Limitations](#limitations)
//! section.
//!
//! <br/>
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
//!
//! This attribute successively substitutes the first identifier of the list (`T`), which is used as a
//! type in the attached source code, with each of the following types (`type1`, `type2`, `type3`)
//! to generate all the variations.
//!
//! The code must of course be compatible with all the types, or the compiler will trigger the
//! relevant errors. For example `#[trait_gen(T -> u64, f64)]` cannot be used with `Self(0)` because
//! `0` is not a valid floating-point literal.
//!
//! <br/>
//!
//! ## Alternative format
//!
//! The attribute supports a shorter "legacy" format which was used in the earlier versions:
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
//! then the original code is implemented. This is a shortcut for the equivalent format:
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
//! _Remark: this strange ordering comes from an optimization in the legacy format, where the macro
//! stores the code with the first type, writes it for the other types in their declaration order, then
//! adds the original code at the end. This makes no difference, except the order of the compiler
//! messages if there are warnings or errors in the code - that's the only reason we mention it here._
//!
//! The short format can be used when there is little risk of confusion, like in the example below.
//! `Meter` is unlikely to be used in all the variations, so using an alias is unnecessary. The type
//! to replace in the code must be in first position after the attribute:
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
//! <br/>
//!
//! ## Code awareness issues
//!
//! Not all IDEs support procedural macros for code awareness yet, which removes some benefits
//! of using this macro. For example, IntelliJ won't be able to provide any support while typing the
//! code, nor will it be able to look for the definition of the implemented methods when they are
//! used later.
//!
//! There are two work-arounds:
//!
//! * Defining an alias for the identifier used in the attribute:
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
//!   Defining `T` doesn't change the produced code, but it allows the editor to understand it without
//!   expanding the macro.
//!
//! * Implementing for an existing type, and using it as the first identifier:
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
//!   This is somewhat more confusing to read, and doesn't work if `u32` must remain in all the
//!   variations, like the `u64` it the previous example just above.
//!
//! <br/>
//!
//! ## Limitations
//!
//! * Rust doesn't allow alias constructors, like `T(1.0)` in the code below. When it is needed,
//!   `Self` or a trait associated type is usually equivalent: here, `Self(1.0)`. In the rare event
//!   that no substitute is available, consider using the `Default` trait or creating a specific one.
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
//!   The same remains true with the other attribute format, because of a limitation in procedural
//!   macros, which would make the substitution too risky. In short, there is no way to tell whether
//!   `T` is a type to be substituted or something else:
//!
//!   ```rust,compile_fail
//!   # use trait_gen::trait_gen;
//!   # trait Neutral { fn mul_neutral(&self) -> Self; }
//!   # struct Foot(f64);
//!   # struct Mile(f64);
//!   # struct Meter(f64);
//!   #[trait_gen(T -> Meter, Foot, Mile)]
//!   impl Neutral for T {
//!       fn mul_neutral(&self) -> Self {
//!           T(1.0)  // <== ERROR, use Self(1.0) instead
//!       }
//!   }
//!   ```
//!
//! * The macro doesn't handle scopes, so it doesn't support any type declaration with the same name
//! as the type that must be substituted. This, for instance, fails to compile:
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
//! * If the `T` identifier above is only a part of the type path, then it is fine. For example,
//! `super::T`, `T<u64>` or `T(u64)` will not be replaced when using `#[trait_gen(T, ...)]`. But on the other
//! hand, those type paths cannot be substituted either (yet) - you cannot use
//! `#[trait_gen(T<u64>, ...)]` or `#[trait_gen(super::T, ...)]`. This can be worked around by using
//! type aliases or a `use` clause.

use proc_macro::TokenStream;
use proc_macro2::Ident;
use proc_macro_error::{proc_macro_error, abort};
use quote::quote;
use syn::{Generics, GenericParam, Token, parse_macro_input, File, TypePath};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;

#[derive(Debug)]
struct Types {
    current_type: Ident,
    new_types: Vec<Ident>,
    current_defined: bool
}

impl VisitMut for Types {
    fn visit_generics_mut(&mut self, i: &mut Generics) {
        for t in i.params.iter() {
            match &t {
                GenericParam::Type(t) => {
                    if t.ident == self.current_type {
                        abort!(t.span(),
                            "Type '{}' is reserved for the substitution.", self.current_type.to_string();
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

    fn visit_type_path_mut(&mut self, i: &mut TypePath) {
        let TypePath { path, .. } = i;

        // The complete path can be obtained with:
        // let pathname: String = path.segments.iter().map(|p| p.ident.to_string()).collect::<Vec<_>>().join("::");
        //
        // Alternatively, `path.get_ident()`, returns Some(name) when there is only one segment, like `T`,
        // or None if there are multiple segments, like `super::T`.
        //
        // If we want to support segments in the macro arguments, we have to change the type of
        // Types::current_type to TypePath (Punctuated doesn't include colon prefixes), and
        // perform a different replacement here.
        //
        // For now, we constrain the type to be substituted to be a simple identifier.

        // debug code:
        //
        // let idstr = if let Some(id) = path.get_ident() {
        //     id.to_string()
        // } else {
        //     "N/A".to_string()
        // };
        // let pathname: String = path.segments.iter().map(|p| p.ident.to_string()).collect::<Vec<_>>().join("::");
        // println!("path = {} or {}", pathname, idstr);

        if let Some(ident) = path.get_ident() {
            // if we have a simple identifier (no "::", no "<...>", no "(...)"), replaces it if it matches:
            if ident == &self.current_type {
                for mut s in path.segments.iter_mut() {
                    let ident: &mut Ident = &mut (s.ident);
                    if ident == &self.current_type {
                        s.ident = self.new_types.first().unwrap().clone();
                        break
                    }
                }
            }
        }
    }
}


impl Parse for Types {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        if input.peek2(Token![->]) {
            let current_type = input.parse::<Ident>()?;
            input.parse::<Token![->]>()?;
            let vars = Punctuated::<Ident, Token![,]>::parse_terminated(input)?;
            let new_types: Vec<Ident> = vars.into_iter().collect();
            // println!("{} => {}", 
            //     current_type,
            //     new_types.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(", ")
            // );
            Ok(Types { current_type, new_types, current_defined: false })
        } else {
            let vars = Punctuated::<Ident, Token![,]>::parse_terminated(input)?;
            let mut new_types: Vec<Ident> = vars.into_iter().collect();
            let current_type = new_types.remove(0);
            Ok(Types { current_type, new_types, current_defined: true })
        }
    }
}

/// Generates the attached trait implementation for all the types given in parameter.
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
///         Self(self.0 + rhs.0)
///     }
/// }
/// ```
///
/// This attribute successively substitutes the first identifier of the list (`T`), which is used
/// as a type in the attached source code, with each of the following types (`Meter`, `Foot`, `Mile`)
/// to generate all the variations.
///
/// <br/>
///
/// ## Alternative format
///
/// The attribute supports a shorter format which was used when there is little risk of confusion
/// about the type to be substituted in the attached code.
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
/// * Rust doesn't allow alias constructors, like `T(1.0)` in the code below. When it is needed,
///   `Self` or a trait associated type is usually equivalent: here, `Self(1.0)`. In the rare event
///   that no substitute is available, consider using the `Default` trait or creating a specific one.
///
///   ```rust,ignore
///   type T = Meter;
///
///   #[trait_gen(T, Foot, Mile)]
///   impl Neutral for T {
///       fn mul_neutral(&self) -> Self {
///           T(1.0)  // <== ERROR, use Self(1.0) instead
///       }
///   }
///   ```
///
///   The same remains true with the other attribute format, because of a limitation in procedural
///   macros, which would make the substitution too risky. In short, there is no way to tell whether
///   `T` is a type to be substituted or something else:
///
///   ```rust,compile_fail
///   #[trait_gen(T -> Meter, Foot, Mile)]
///   impl Neutral for T {
///       fn mul_neutral(&self) -> Self {
///           T(1.0)  // <== ERROR, use Self(1.0) instead
///       }
///   }
///   ```
///
/// * The macro doesn't handle scopes, so it doesn't support any type declaration with the same name
/// as the type that must be substituted. This, for instance, fails to compile:
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
/// * If the `T` identifier above is only a part of the type path, then it is fine. For example,
/// `super::T`, `T<u64>` or `T(u64)` will not be replaced when using `#[trait_gen(T, ...)]`. But on the other
/// hand, those type paths cannot be substituted either (yet) - you cannot use
/// `#[trait_gen(T<u64>, ...)]` or `#[trait_gen(super::T, ...)]`. This can be worked around by using
/// type aliases or a `use` clause.
#[proc_macro_attribute]
#[proc_macro_error]
pub fn trait_gen(args: TokenStream, item: TokenStream) -> TokenStream {
    // let input = parse_macro_input!(item as ItemImpl);
    let ast: File = syn::parse(item).unwrap();
    let mut types = parse_macro_input!(args as Types);
    let mut output = TokenStream::new();
    while !types.new_types.is_empty() {
        let mut modified_ast = ast.clone();
        types.visit_file_mut(&mut modified_ast);
        output.extend(TokenStream::from(quote!(#modified_ast)));
        types.new_types.remove(0);
    }
    if types.current_defined {
        output.extend(TokenStream::from(quote!(#ast)));
    }
    output
}
