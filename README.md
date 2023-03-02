# trait-gen

[![crate](https://img.shields.io/crates/v/trait_gen.svg)](https://crates.io/crates/trait-gen)
[![documentation](https://docs.rs/trait-gen/badge.svg)](https://docs.rs/trait-gen)
[![build status](https://github.com/blueglyph/trait_gen/actions/workflows/master.yml/badge.svg)](https://github.com/blueglyph/trait_gen/actions)
[![crate](https://img.shields.io/crates/l/trait_gen.svg)](https://github.com/blueglyph/trait_gen/blob/master/LICENSE-MIT)

<hr/>

<!-- TOC -->
* [trait-gen](#trait-gen)
* [The trait_gen attribute](#the-traitgen-attribute)
  * [Examples](#examples)
  * [Alternative format](#alternative-format)
  * [Code awareness issues](#code-awareness-issues)
  * [Limitations](#limitations)
* [Compatibility](#compatibility)
* [Releases](#releases)
* [License](#license)
<!-- TOC -->

<hr/>

This library provides attributes to generate the trait implementations for several
types, without the need for custom declarative macros.

In the example below, the `Add` trait is implemented for `Meter`, `Foot` and `Mile`. The
`T` type identifier is used to mark where the substitution takes place; it can be an existing type
or alias but it's not mandatory.

```rust
use trait_gen::trait_gen;

pub struct Meter(f64);
pub struct Foot(f64);
pub struct Mile(f64);

#[trait_gen(T -> Meter, Foot, Mile)]
impl Add for T {
    type Output = T;

    fn add(self, rhs: T) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}
```

The `trait_gen` attribute has the same effect as this custom declarative macro:

```rust
macro_rules! impl_add_length {
    ($($t:ty)*) => (
        $(impl Add for $t {
            type Output = $t;

            fn add(self, rhs: $t) -> Self::Output {
                Self(self.0 + rhs.0)
            }
        })*
    )
}

impl_add_length! { Meter Foot Mile }
```

The advantages of the first method are the clarity of the native code, the support of
refactoring tools, editor syntactic and semantic awareness, and not having to convert the code into 
a declarative macro. Looking for the definition of an implementation method is 
also much easier with the full support of code-aware editors!

The disadvantage is the current lack of support for procedural macros with the _IntelliJ_ plugin,
although this is an ongoing work (see [tracking issue](https://github.com/intellij-rust/intellij-rust/issues/6908)). A few work-arounds are discussed [later](#code-awareness-issues).

There are also a few limitations of the current version described in the [Limitations](#limitations)
section.

# The trait_gen attribute

```rust
#[trait_gen(T -> type1, type2, type3)]
impl Trait for T {
    // ...
}
```

This attribute successively substitutes the `T` type parameter, which is used as a
type in the attached source code, with each of the following types (`type1`, `type2`, `type3`) 
to generate all the implementations.

All paths beginning with `T` in the code have this segment replaced. For example, 
`T::default()` generates `type1::default()`, `type2::default()` and so on, but 
`super::T` is unchanged.

The code must of course be compatible with all the types, or the compiler will trigger the
relevant errors. For example `#[trait_gen(T -> u64, f64)]` cannot be used with `Self(0)` because
`0` is not a valid floating-point literal.

## Examples

Here are a few examples of the substitutions that are supported.

```rust
#[trait_gen(U -> u32, i32)]
impl AddMod for U {
    fn add_mod(self, other: U, m: U) -> U {
        const U: U = 0;
        let zero = U::default();
        let offset: super::U = super::U(0);
        (self + other + U + zero + offset.0 as U) % m
    }
}
```

- is expanded into:

    ```rust
    impl AddMod for u32 {
        fn add_mod(self, other: u32, m: u32) -> u32 {
            const U: u32 = 0;
            let zero = u32::default();
            let offset: super::U = super::U(0);
            (self + other + U + zero + offset.0 as u32) % m
        }
    }
    ```
  (and the same for `i32`)

This code, with `struct Meter(f64)`, `struct Foot(f64)` and so on:

```rust
#[trait_gen(T -> Meter, Foot, Mile)]
impl Add for T {
    type Output = T;

    fn add(self, rhs: T) -> Self::Output {
        const T: f64 = 0.0;
        T(self.0 + rhs.0 + T)
    }
}
```

- is expanded into:

    ```rust
    impl Add for Meter {
        type Output = Meter;
  
        fn add(self, rhs: Meter) -> Self::Output {
            const T: f64 = 0.0;
            Meter(self.0 + rhs.0 + T)
        }
    }
    ```
  (and the same for `Foot` and `Mile`)

The same expansion can be performed on tuples or other struct types.

## Alternative format

The attribute supports a shorter "legacy" format which was used in the earlier versions:

```rust
#[trait_gen(type1, type2, type3)]
impl Trait for type1 {
    // ...
}
```

Here, `type2` and `type3` are literally substituted for `type1` to generate their implementation,
then the original code is implemented for `type1`. This is a shortcut for the equivalent attribute
with the other format:

```rust
#[trait_gen(type1 -> type2, type3, type1)]
impl Trait for type1 {
    // ...
}
```

_Remark: this strange ordering comes from an optimization in the legacy format. This makes no
difference, except the order of the compiler messages if there are warnings or errors in the
code - that's the only reason we mention it here._

The short format can be used when there is no risk of confusion, like in the example below.
All the `Meter` instances must change, it is unlikely to be mixed with `Foot` and `Mile`, so 
using an alias is unnecessary. The type to replace in the code must be in first position in
the parameter list:

```rust
use std::ops::Add;
use trait_gen::trait_gen;

pub struct Meter(f64);
pub struct Foot(f64);
pub struct Mile(f64);

#[trait_gen(Meter, Foot, Mile)]
impl Add for Meter {
    type Output = Meter;

    fn add(self, rhs: Meter) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}
```

In some situations, one of the implemented types happens to be required in all the
implementations. Consider the following example, in which the return type is always `u64`:

```rust
pub trait ToU64 {
    fn into_u64(self) -> u64;
}

#[trait_gen(u64, i64, u32, i32, u16, i16, u8, i8)]
impl ToU64 for u64 {
    fn into_u64(self) -> u64 {  // ERROR! Replaced by -> i64, u32, ...
        self as u64
    }
}
```

This doesn't work because the return type of `into_u64()` will be replaced too! To prevent it,
an alias must be used (or the other attribute format). This works:

```rust
type T = u64;

#[trait_gen(T, i64, u32, i32, u16, i16, u8, i8)]
impl ToU64 for T {
    fn into_u64(self) -> u64 {
        self as u64
    }
}
```

That is how the other format came to be, by getting rid of the type alias and allowing a "local"
type parameter:

```rust
#[trait_gen(T -> u64, i64, u32, i32, u16, i16, u8, i8)]
fn ToU64 for T { /* ... */ }
```

## Code awareness issues

_rust-analyzer_ supports procedural macros for code awareness, so everything should be fine for
editors based on this Language Server Protocol implementation. Unfortunately this isn't the 
case of all IDEs yet, which removes some benefits of using this macro. For instance, the 
_IntelliJ_ plugin is not able to provide much support while typing the code for an unknown 
`T` type, nor can it find the definition of the implemented methods, or even 
suggest them.

Here are two work-arounds that help when typing the trait implementation. However, they can't
do much about code awareness when the trait methods are used later. Hopefully the remaining
IDEs will provide more support for procedural macros soon.

* Defining a type alias for the identifier used in the attribute doesn't change the produced
code, but it allows the editor to understand it without expanding the macro:

  ```rust
    pub trait ToU64 {
        fn into_u64(self) -> u64;
    }

    type T = u64;
  
    #[trait_gen(T -> u64, i64, u32, i32, u16, i16, u8, i8)]
    impl ToU64 for T {
        fn into_u64(self) -> u64 {
            self as u64
        }
    }
  ```
  
* Implementing for an existing type then using it as the type parameter is another possibility,
but it may look more confusing so use it with caution:

  ```rust
    pub trait AddMod {
        fn add_mod(self, other: Self, m: Self) -> Self;
    }

    // No need to use `type T = u32` in such a simple case:
    #[trait_gen(u32 -> u32, i32, u64, i64, f32, f64)]
    impl AddMod for u32 {
        fn add_mod(self, other: Self, m: Self) -> Self {
            (self + other) % m
        }
    }
  ```

## Limitations

* Rust doesn't allow alias constructors with the "legacy" format. `Self` or a trait associated
type is usually equivalent - here, `Self(1.0)`. If there is no alternative, consider using 
the `Default` trait or creating a specific one.

  ```rust
  type T = Meter;
  
  #[trait_gen(T, Foot, Mile)]
  impl Neutral for T {
      fn mul_neutral(&self) -> Self {
          T(1.0)  // <== ERROR, use Self(1.0) instead
      }
  }
  ```
  
  The other attribute format allows the substitution: 

  ```rust
  #[trait_gen(T -> Meter, Foot, Mile)]
  impl Neutral for T {
      fn mul_neutral(&self) -> Self {
          T(1.0)  // <== replaced
      }
  }
  ```

* The attribute doesn't handle scopes, so it doesn't support any type declaration with the same name
as the type that must be substituted, including generics. This, for instance, fails to compile:

  ```rust
  use num::Num;
  use trait_gen::trait_gen;
  
  trait AddMod {
      type Output;
      fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output;
  }
  
  #[trait_gen(T -> u64, i64, u32, i32)]
  impl AddMod for T {
      type Output = T;
  
      fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output {
          fn int_mod<T: Num> (a: T, m: T) -> T { // <== ERROR, conflicting 'T'
              a % m
          }
          int_mod(self + rhs, modulo)
      }
  }
  ```

* Substitutions are limited to single segments, like `Meter`. They don't support multiple
segments or arguments, like `super::Meter` or `Meter<f64>`. The same applies to the attribute
parameter: `T -> ...` is allowed, but not `super::T -> ...`. This can be worked around by 
using a type alias or a `use` clause.

# Compatibility

The `trait-gen` crate is tested for rustc 1.67.1 and greater, on Windows 64-bit and Linux 64/32-bit platforms. There shouldn't be any problem with older versions.

# Releases

[RELEASES.md](RELEASES.md) keeps a log of all the releases.

# License

Licensed under [MIT license](https://choosealicense.com/licenses/mit/).
