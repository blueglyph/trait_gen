# trait-gen

[![crate](https://img.shields.io/crates/v/trait_gen.svg)](https://crates.io/crates/trait-gen)
[![documentation](https://docs.rs/trait-gen/badge.svg)](https://docs.rs/trait-gen)
[![build status](https://github.com/blueglyph/trait_gen/actions/workflows/master.yml/badge.svg)](https://github.com/blueglyph/trait_gen/actions)
[![crate](https://img.shields.io/crates/l/trait_gen.svg)](https://github.com/blueglyph/trait_gen/blob/master/LICENSE-MIT)

This library provides attributes to generate the trait implementations for several
types, without the need for custom declarative macros.

For example,

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
refactoring tools, editor syntactic awareness, and not having to convert the code to 
the declarative macro syntax. Looking for the definition of an implementation method is 
also much easier with the full support of code-aware editors!

The disadvantage is the current lack of support for procedural macros with the IntelliJ plugin,
although this is an ongoing work (see [tracking issue](https://github.com/intellij-rust/intellij-rust/issues/6908)). A few work-arounds are discussed [later](#code-awareness-issues).

There are also a few limitations of the current version described in the [Limitations](#limitations)
section.

## The trait_gen attribute

```rust
#[trait_gen(T -> type1, type2, type3)]
impl Trait for T {
    // ...
}
```

This attribute successively substitutes the first identifier of the list (`T`), which is used as a
type in the attached source code, with each of the following types (`type1`, `type2`, `type3`) 
to generate all the variations.

The code must of course be compatible with all the types, or the compiler will trigger the
relevant errors. For example `#[trait_gen(T -> u64, f64)]` cannot be used with `Self(0)` because
`0` is not a valid floating-point literal.

## Alternative format

The attribute supports a shorter "legacy" format which was used in the earlier versions:
```rust
#[trait_gen(type1, type2, type3)]
impl Trait for type1 {
    // ...
}
```

Here, `type2` and `type3` are literally substituted for `type1` to generate their implementation, then the original code is implemented. This is a shortcut for the equivalent format:

```rust
#[trait_gen(type1 -> type2, type3, type1)]
impl Trait for type1 {
    // ...
}
```

_Remark: this strange ordering comes from an optimization in the legacy format, where the macro
stores the code with the first type, writes it for the other types in their declaration order, then 
adds the original code at the end. This makes no difference, except the order of the compiler
messages if there are warnings or errors in the code - that's the only reason we mention it here._

The short format can be used when there is little risk of confusion, like in the example below.
`Meter` is unlikely to be used in all the variations, so using an alias is unnecessary. The type
to replace in the code must be in first position after the attribute:

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

## Code awareness issues

Not all IDEs support procedural macros for code awareness yet, which removes some benefits
of using this macro. For example, IntelliJ won't be able to provide any support while typing the
code, nor will it be able to look for the definition of the implemented methods when they are 
used later.

There are two work-arounds:

* Defining an alias for the identifier used in the attribute:
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
  Defining `T` doesn't change the produced code, but it allows the editor to understand it without
  expanding the macro. 

* Implementing for an existing type, and using it as the first identifier:
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
  This is somewhat more confusing to read, and doesn't work if `u32` must remain in all the
  variations, like the `u64` it the previous example just above.

## Limitations

* Rust doesn't allow alias constructors, like `T(1.0)` in the code below. When it is needed,
  `Self` or a trait associated type is usually equivalent: here, `Self(1.0)`. In the rare event
  that no substitute is available, consider using the `Default` trait or creating a specific one.

  ```rust
  type T = Meter;
  
  #[trait_gen(T, Foot, Mile)]
  impl Neutral for T {
      fn mul_neutral(&self) -> Self {
          T(1.0)  // <== ERROR, use Self(1.0) instead
      }
  }
  ```
  The same remains true with the other attribute format, because of a limitation in procedural
  macros, which would make the substitution too risky. In short, there is no way to tell whether
  `T` is a type to be substituted or something else:
  ```rust
  #[trait_gen(T -> Meter, Foot, Mile)]
  impl Neutral for T {
      fn mul_neutral(&self) -> Self {
          T(1.0)  // <== ERROR, use Self(1.0) instead
      }
  }
  ```

* The macro doesn't handle scopes, so it doesn't support any type declaration with the same name
as the type that must be substituted. This, for instance, fails to compile:

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

* If the `T` identifier above is only a part of the type path, then it is fine. For example,
`super::T`, `T<u64>` or `T(u64)` will not be replaced when using `#[trait_gen(T, ...)]`. But on the other
hand, those type paths cannot be substituted either (yet) - you cannot use
`#[trait_gen(T<u64>, ...)]` or `#[trait_gen(super::T, ...)]`. This can be worked around by using
type aliases or a `use` clause.

## Compatibility

The `trait-gen` crate is tested for rustc 1.67.1 and greater, on Windows 64-bit and Linux 64/32-bit platforms. There shouldn't be any problem with older versions.

## Releases

[RELEASES.md](RELEASES.md) keeps a log of all the releases.

## License

Licensed under [MIT license](https://choosealicense.com/licenses/mit/).
