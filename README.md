# trait-gen

[![crate](https://img.shields.io/crates/v/trait_gen.svg)](https://crates.io/crates/trait-gen)
[![documentation](https://docs.rs/trait_gen/badge.svg)](https://docs.rs/trait-gen)
[![build status](https://github.com/blueglyph/trait_gen/actions/workflows/master.yml/badge.svg)](https://github.com/blueglyph/trait_gen/actions)
[![crate](https://img.shields.io/crates/l/trait_gen.svg)](https://github.com/blueglyph/trait_gen/blob/master/LICENSE-MIT)

This library provides procedural macros to generate the trait implementations for several
types, without the need for custom declarative macros. For example,

```rust
use trait_gen::trait_gen;

pub trait IntoU64 {
    fn into_u64(self) -> u64;
}

type T = u64;

#[trait_gen(T, i64, u32, i32, u16, i16, u8, i8)]
impl IntoU64 for T {
    fn into_u64(self) -> u64 {
        self as u64
    }
}
```

has the same effect as

```rust
pub trait IntoU64 {
    fn into_u64(self) -> u64;
}

macro_rules! impl_into_u64 {
    ($($t:ty)*) => (
        $(impl IntoU64 for $t {
            fn into_u64(self) -> u64 {
                self as u64
            }
        })*
    )
}

impl_into_u64! { u64 i64 u32 i32 u16 i16 u8 i8 }
```

The advantage of the first method is the clarity of the native code, the support of
refactoring tools, code awareness, and not having to convert the code to the declarative
macro syntax.

The disadvantage is the lack of support for declarative macros with the IntelliJ plugin,
although this is an ongoing work (see [tracking issue](https://github.com/intellij-rust/intellij-rust/issues/6908)). There are also a few limitations of the current version described in the [Limitations](#limitations) section.

## The trait_gen macro

```rust
#[trait_gen(type1, type2, type3)]
impl Trait for type1 {
    // ...
}
```

This macro successively substitutes the first type of the list (`type1`), which is used in the
attached source code, with each of the following types (`type2`, `type3`) to generate all the
variations. So the `#[trait_gen(u64, i64, u32, i32)]` attribute implements the original source
code, then looks for all "`u64`" types and literally replaces them with `i64`, `u32` and `i32`
to generate the four implementations.

The code must of course be compatible with all the types, or the compiler will trigger the
relevant errors. For example `#[trait_gen(u64, f64)]` cannot be used with `Self(0)` because `0`
is not a valid floating-point literal.

To avoid any confusion in the attached code between the type to be substituted and
possible instances of the same type that must remain in all variations, it is recommended to use
an alias `type T = <type>` and give `T` as first parameter, like in the first example below.
This has the other advantage of improving the clarity. In the same example, using
`#[trait_gen(u64, i64, u32, ...)]` with `fn into_u64(self) -> u64` would defeat the purpose of the
method by returning `i64`, `u32`, ... instead of always returning a `u64`.

## Examples

This example shows how to keep the `u64` type in all the implementations by using an alias to
indicate what must be substituted. The types are parsed literally, which makes it possible, but
this is also why there must not be any other `T` instance used in a generic, for example (see
[Limitations](#limitations) for more details).

```rust
use trait_gen::trait_gen;

pub trait ToU64 {
    fn into_u64(self) -> u64;
}

type T = u64;

#[trait_gen(T, i64, u32, i32, u16, i16, u8, i8)]
impl ToU64 for T {
    fn into_u64(self) -> u64 {
        self as u64
    }
}
```

When there is little risk of confusion in the example below, because `Meter` type is unlikely
to be used in all the variations. In that case, using an alias is unnecessary.

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

## Limitations

* Rust doesn't allow alias constructors, like `T(1.0)` in the code below. When it is needed,
  `Self` or a trait associated type is usually equivalent: here, `Self(1.0)`. In the rare event
  that no substitute is available, consider using the `Default` trait or creating a specific one.


```rust
#[trait_gen(T, Foot, Mile)]
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

type T = u64;

#[trait_gen(T, i64, u32, i32)]
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

## Notes

* The implementation order may vary; currently the types are taken in the given order
excepted for the first type used in the source code, which is the last to be
generated. This may change in the future, but it only impacts when possible warnings or errors
are generated by the compiler or the linter.

* The `type T = MyType` being on another line masks the generated types a little, when we
see for example `#[trait_gen(T, i64, u32, i32)]`. That is why the best place for the alias
declaration is right above the macro.

## Usage

Add this dependency to your `Cargo.toml` file:

```toml
[dependencies]
trait-gen = "0"
```

## Compatibility

The `trait-gen` crate is tested for rustc 1.67.1 and greater, on Windows 64-bit and Linux 64/32-bit platforms. There shouldn't be any problem with older versions.

## Releases

[RELEASES.md](RELEASES.md) keeps a log of all the releases.

## License

Licensed under [MIT license](https://choosealicense.com/licenses/mit/).
