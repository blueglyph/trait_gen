// Copyright (c) 2025 Redglyph (@gmail.com). All Rights Reserved.
//
// Publicly exposed macros.

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
mod lib_macros;
mod subst;
mod args;
mod utils;

use proc_macro::TokenStream;
use proc_macro_error2::proc_macro_error;
use crate::lib_macros::{macro_trait_gen, macro_trait_gen_if};

//==============================================================================
// Substitution attributes

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
    macro_trait_gen(args.into(), item.into()).into()
}

#[cfg(not(feature = "no_type_gen"))]
/// Generates the attached implementation code for all the types given in argument.
///
/// This is a synonym of the [trait_gen()] attribute, provided because the attribute can be used with
/// other elements than trait implementations.
#[proc_macro_attribute]
#[proc_macro_error]
pub fn type_gen(args: TokenStream, item: TokenStream) -> TokenStream {
    macro_trait_gen(args.into(), item.into()).into()
}

//==============================================================================
// Conditional attributes

/// Generates the attached code if the condition is met.
///
/// Please refer to the [crate documentation](crate#conditional-code).
#[proc_macro_attribute]
#[proc_macro_error]
pub fn trait_gen_if(args: TokenStream, item: TokenStream) -> TokenStream {
    macro_trait_gen_if("trait_gen_if", args.into(), item.into()).into()
}

#[cfg(not(feature = "no_type_gen"))]
/// Generates the attached code if the condition is met.
///
/// This is a synonym of the [trait_gen_if()] attribute, provided because the attribute can be used with
/// other elements than trait implementations.
///
/// Please refer to the [crate documentation](crate#conditional-code).
#[proc_macro_attribute]
#[proc_macro_error]
pub fn type_gen_if(args: TokenStream, item: TokenStream) -> TokenStream {
    macro_trait_gen_if("type_gen_if", args.into(), item.into()).into()
}
