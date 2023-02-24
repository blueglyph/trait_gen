// Copyright 2023 Redglyph

//! # The typegen library
//!
//! This library provides procedural macros to generate the trait implementations for several
//! types, without the need for custom declarative macros. For example,
//!
//! ```
//! use typegen::typegen;
//!
//! pub trait IntoU64 {
//!     fn into_u64(self) -> u64;
//! }
//!
//! type T = u64;
//!
//! #[typegen(T, i64, u32, i32, u16, i16, u8, i8)]
//! impl IntoU64 for T {
//!     fn into_u64(self) -> u64 {
//!         self as u64
//!     }
//! }
//! ```
//!
//! has the same effect as
//!
//! ```
//! pub trait IntoU64 {
//!     fn into_u64(self) -> u64;
//! }
//!
//! macro_rules! impl_into_u64 {
//!     ($($t:ty)*) => (
//!         $(impl IntoU64 for $t {
//!             fn into_u64(self) -> u64 {
//!                 self as u64
//!             }
//!         })*
//!     )
//! }
//!
//! impl_into_u64! { u64 i64 u32 i32 u16 i16 u8 i8 }
//! ```
//!
//! The advantage of the first method is the clarity of the native code, the support of
//! refactoring tools, code awareness, and not having to convert the code to the declarative
//! macro syntax.
//!
//! The disadvantage is the lack of support for declarative macros with the IntelliJ plugin,
//! although this is an ongoing work (see [tracking issue](https://github.com/intellij-rust/intellij-rust/issues/6908)).
//!
//! <br/>
//!
//! # The typegen macro
//!
//! ```ignore,rust
//! #[typegen(type1, type2, type3)]
//! impl Trait for type1 {
//!     // ...
//! }
//! ```
//!
//! This macro successively substitutes the first type of the list (`type1`), which is used in the
//! attached source code, with each of the following types (`type2`, `type3`) to generate all the
//! variations. So the `#[typegen(u64, i64, u32, i32)]` attribute implements the original source
//! code, then looks for all "`u64`" types and literally replaces them with `i64`, `u32` and `i32`
//! to generate the four implementations.
//!
//! <br/>
//!
//! The code must of course be compatible with all the types, or the compiler will trigger the
//! relevant errors. For example `#[typegen(u64, f64)]` cannot be used with `Self(0)` because `0`
//! is not a valid floating-point literal.
//!
//! <br/>
//!
//! To avoid any confusion in the attached code between the type to be substituted and
//! possible instances of the same type that must remain in all variations, it is recommended to use
//! an alias `type T = <type>` and give `T` as first parameter, like in the first example below.
//! This has the other advantage of improving the clarity. In the same example, using
//! `#[typegen(u64, i64, u32, ...)]` with `fn into_u64(self) -> u64` would defeat the purpose of the
//! method by returning `i64`, `u32`, ... instead of always returning a `u64`.
//!
//! <br/>
//!
//! ## Examples
//!
//! This example shows how to keep the `u64` type in all the implementations by using an alias to
//! indicate what must be substituted. The types are parsed literally, which makes it possible, but
//! this is also why there must not be any other `T` instance used in a generic, for example (see
//! [Limitations](#limitations) for more details).
//!
//! ```
//! use typegen::typegen;
//!
//! pub trait ToU64 {
//!     fn into_u64(self) -> u64;
//! }
//!
//! type T = u64;
//!
//! #[typegen(T, i64, u32, i32, u16, i16, u8, i8)]
//! impl ToU64 for T {
//!     fn into_u64(self) -> u64 {
//!         self as u64
//!     }
//! }
//! ```
//!
//! When there is little risk of confusion in the example below, because `Meter` type is unlikely
//! to be used in all the variations. In that case, using an alias is unnecessary.
//!
//! ```
//! use std::ops::Add;
//! use typegen::typegen;
//!
//! pub struct Meter(f64);
//! pub struct Foot(f64);
//! pub struct Mile(f64);
//!
//! #[typegen(Meter, Foot, Mile)]
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
//! ## Limitations
//!
//! * Rust doesn't allow alias constructors, like `T(1.0)` in the code below. When it is needed,
//!   `Self` or a trait associated type is usually equivalent: here, `Self(1.0)`. In the rare event
//!   that no substitute is available, consider using the `Default` trait or creating a specific one.
//!
//!
//! ```compile_fail,rust
//! # use typegen::typegen;
//! # trait Neutral { fn mul_neutral(&self) -> Self; }
//! # struct Foot(f64);
//! # struct Mile(f64);
//! # struct Meter(f64);
//! # type T = Meter;
//! #[typegen(T, Foot, Mile)]
//! impl Neutral for T {
//!     fn mul_neutral(&self) -> Self {
//!         T(1.0)  // <== ERROR, use Self(1.0) instead
//!     }
//! }
//! ```
//!
//! * The macro doesn't handle scopes, so it doesn't support any type declaration with the same name
//! as the type that must be substituted. This, for instance, fails to compile:
//!
//! ```compile_fail,rust
//! use num::Num;
//! use typegen::typegen;
//!
//! trait AddMod {
//!     type Output;
//!     fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output;
//! }
//!
//! type T = u64;
//!
//! #[typegen(T, i64, u32, i32)]
//! impl AddMod for T {
//!     type Output = T;
//!
//!     fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output {
//!         fn int_mod<T: Num> (a: T, m: T) -> T { // <== ERROR, conflicting 'T'
//!             a % m
//!         }
//!         int_mod(self + rhs, modulo)
//!     }
//! }
//! ```
//!
//! * If the `T` identifier above is only a part of the type path, then is safe to use. For example,
//! `super::T`, `T<u64>` or `T(u64)` will not be replaced by `#[typegen(T, ...)]`. But on the other
//! hand, those type paths cannot be substituted either (yet) -- you cannot use
//! `#[typegen(T<u64>, ...)]` or `#[typegen(super::T, ...)]`. This can be worked around by using
//! type aliases or a `use` clause.
//!
//! <br/>
//!
//! # Remarks
//!
//! * The implementation order may vary; currently the types are taken in the given order
//! excepted for the first type used in the source code, which is the last to be
//! generated. This may change in the future, but it only impacts when possible warnings or errors
//! are generated by the compiler or the linter.
//!
//! * The `type T = MyType` being on another line masks the generated types a little, when we
//! see for example `#[typegen(T, i64, u32, i32)]`. That is why the best place for the alias
//! declaration is right above the macro.

use proc_macro_error::proc_macro_error;
use proc_macro::TokenStream;
use proc_macro2::Ident;
use proc_macro_error::abort;

use syn::{ItemImpl, PathSegment, Generics, parse_quote, GenericParam, Token, parse_macro_input};
use quote::quote;
use syn::fold::Fold;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;

#[derive(Debug)]
struct Types {
    current_type: Ident,
    new_types: Vec<Ident>
}

impl Fold for Types {

    /// Triggers an error when a generic with the same name type is used:
    fn fold_generics(&mut self, i: Generics) -> Generics {
        for t in i.params.iter() {
            match &t {
                GenericParam::Type(t) => {
                    if t.ident == self.current_type {
                        abort!(t.span(),
                            "Type '{}' is reserved for the substitution.", self.current_type.to_string();
                            help = "Use another identifier for this local generic type."
                        );

                        // Other ways to generate an error message:

                        // Yet another unstable feature: (but would be preferrable)
                        // ----------------------------
                        // t.span().unwrap()
                        //     .error(ERROR_MSG)
                        //     .emit();

                        // This doesn't work well because it has to be inserted at the right
                        // spot to avoid generating a syntax error (hard with folds):
                        // --------------------------------------------------------------------
                        // return parse_quote_spanned!{
                        //     i.span() => compile_error!(ERROR_MSG)
                        // }
                        //
                        // or
                        //
                        // return parse_quote_spanned!(t.span() =>
                        //     compile_error!(#ERROR_MSG)
                        // );

                        // `panic!` works but doesn't give the location and shows a generic
                        // error message (the useful bit is lower, in the "help" part):
                        // ----------------------------------------------------------------
                        // panic!("{ERROR_MSG}");
                        //
                        // error: custom attribute panicked
                        //   --> tests\integration.rs:25:1
                        //    |
                        // 25 | #[return_as_is]
                        //    | ^^^^^^^^^^^^^^^
                        //    |
                        //    = help: message: Type 'T' is reserved for the substitution. Use ...
                    }
                }
                _ => {}
            }
        }
        i
    }

    fn fold_path_segment(&mut self, ps: PathSegment) -> PathSegment {
        let ident: &Ident = &ps.ident;
        // let args: &PathArguments = &ps.arguments;
        // print!("PathSemgnt.ident: {ident}, args: ");
        // match args {
        //     PathArguments::None => println!("none"),
        //     PathArguments::AngleBracketed(_) => println!("<'a, T>"),
        //     PathArguments::Parenthesized(_) => println!("(A, B) -> C"),
        // };
        if ident == &self.current_type {
            let new_type = self.new_types.first().unwrap();
            parse_quote!(#new_type)
        } else {
            ps
        }
    }
}

impl Parse for Types {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let vars = Punctuated::<Ident, Token![,]>::parse_terminated(input)?;
        let mut new_types: Vec<Ident> = vars.into_iter().collect();
        let current_type = new_types.remove(0);
        Ok(Types { current_type, new_types })
    }
}

/// Generates the attached trait implementation for all the types given in parameter.
///
/// ```ignore,rust
/// #[typegen(type1, type2, type3)]
/// impl Trait for type1 {
///     // ...
/// }
/// ```
///
/// This macro successively substitutes the first type of the list (`type1`), which is used in the
/// attached source code, with each of the following types (`type2`, `type3`) to generate all the
/// variations. So `#[typegen(u64, i64, u32, i32)]` implements the original source code, then
/// looks for all "`u64`" types and literally replaces them with `i64`, `u32` and `i32` to generate
/// the four implementations.
///
/// # Example
///
/// This code generates the trait implementation for i64, u32, i32, u16, i16, u8, i8 and u64:
///
/// ```
/// use typegen::typegen;
///
/// pub trait ToU64 {
///     fn into_u64(self) -> u64;
/// }
///
/// type T = u64;
///
/// #[typegen(T, i64, u32, i32, u16, i16, u8, i8)]
/// impl ToU64 for T {
///     fn into_u64(self) -> u64 {
///         self as u64
///     }
/// }
/// ```
///
/// # Limitations
///
/// * Rust doesn't allow alias constructors, like `T(1.0)` in the code below. When it is needed,
///   `Self` or a trait associated type is usually equivalent: here, `Self(1.0)`. In the rare event
///   that no substitute is available, consider using the `Default` trait or creating a specific one.
///
/// ```compile_fail,rust
/// # use typegen::typegen;
/// # trait Neutral { fn mul_neutral(&self) -> Self; }
/// # struct Foot(f64);
/// # struct Mile(f64);
/// # struct Meter(f64);
/// # type T = Meter;
/// #[typegen(T, Foot, Mile)]
/// impl Neutral for T {
///     fn mul_neutral(&self) -> Self {
///         T(1.0)  // <== ERROR, use Self(1.0) instead
///     }
/// }
/// ```
///
/// * The macro doesn't handle scopes, so it doesn't support any type declaration with the same name
/// as the type that must be substituted. This, for instance, fails to compile:
///
/// ```compile_fail,rust
/// # use typegen::typegen;
/// # type T = u64;
/// #[typegen(T, i64, u32, i32)]
/// impl AddMod for T {
///     type Output = T;
///
///     fn add_mod(self, rhs: Self) -> Self::Output {
///         fn fast_mod<T: Num> (a: T, b: T) { // ... }   // <== ERROR, conflicting 'T'
///         // ...
/// # }}}
/// ```
#[proc_macro_attribute]
#[proc_macro_error]
pub fn typegen(args: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemImpl);
    let mut types = parse_macro_input!(args as Types);
    let mut output = TokenStream::new();
    while !types.new_types.is_empty() {
        let modified = types.fold_item_impl(input.clone());
        output.extend(TokenStream::from(quote!(#modified)));
        types.new_types.remove(0);
    }
    output.extend(TokenStream::from(quote!(#input)));
    output
}

//==================================================================================================

use syn::visit_mut::{VisitMut};
// use syn::{Expr, File, Lit, LitInt, TypePath, Path};
use syn::{File, TypePath};

impl VisitMut for Types {

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

    fn visit_generics_mut(&mut self, i: &mut Generics) {
        for t in i.params.iter() {
            match &t {
                GenericParam::Type(t) => {
                    if t.ident == self.current_type {
                        abort!(t.span(),
                            "Type '{}' is reserved for the substitution.", self.current_type.to_string();
                            help = "Use another identifier for this local generic type."
                        );

                    }
                }
                _ => {}
            }
        }

        // Note: other ways to generate an error message:
        //
        // Yet another unstable feature: (but would be preferrable)
        // ----------------------------
        // t.span().unwrap()
        //     .error(ERROR_MSG)
        //     .emit();
        //
        // This doesn't work well because it has to be inserted at the right
        // spot to avoid generating a syntax error (hard with folds):
        // --------------------------------------------------------------------
        // return parse_quote_spanned!{
        //     i.span() => compile_error!(ERROR_MSG)
        // }
        //
        // or
        //
        // return parse_quote_spanned!(t.span() =>
        //     compile_error!(#ERROR_MSG)
        // );
        //
        // `panic!` works but doesn't give the location and shows a generic
        // error message (the useful bit is lower, in the "help" part):
        // ----------------------------------------------------------------
        // panic!("{ERROR_MSG}");
        //
        // error: custom attribute panicked
        //   --> tests\integration.rs:25:1
        //    |
        // 25 | #[return_as_is]
        //    | ^^^^^^^^^^^^^^^
        //    |
        //    = help: message: Type 'T' is reserved for the substitution. Use ...
    }
}

#[proc_macro_attribute]
#[proc_macro_error]
pub fn typegen2(args: TokenStream, item: TokenStream) -> TokenStream {
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
    output.extend(TokenStream::from(quote!(#ast)));
    output
}

#[cfg(tests)]
mod visit_example {
    use quote::quote;
    use syn::visit_mut::{self, VisitMut};
    use syn::{parse_quote, Expr, File, Lit, LitInt};

    struct BigintReplace;

    impl VisitMut for BigintReplace {
        fn visit_expr_mut(&mut self, node: &mut Expr) {
            if let Expr::Lit(expr) = &node {
                if let Lit::Int(int) = &expr.lit {
                    if int.suffix() == "u256" {
                        let digits = int.base10_digits();
                        let unsuffixed: LitInt = syn::parse_str(digits).unwrap();
                        *node = parse_quote!(bigint::u256!(#unsuffixed));
                        return;
                    }
                }
            }

            // Delegate to the default impl to visit nested expressions.
            visit_mut::visit_expr_mut(self, node);
        }
    }

    #[test]
    fn main() {
        let code = quote! {
            fn main() {
                let _ = 999u256;
            }
        };

        let mut syntax_tree: File = syn::parse2(code).unwrap();
        BigintReplace.visit_file_mut(&mut syntax_tree);
        println!("{}", quote!(#syntax_tree));
    }
}