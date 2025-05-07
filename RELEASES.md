# 2.0.1 (2025-05-07)

- fix a few lint issues

# 2.0.0 (2025-05-07)

- add several permutation formats for typical use-cases:
  - `#[trait_gen(T, U -> u8, u16, u32)]` is a handy shortcut for 
    ```
    #[trait_gen(T -> u8, u16, u32)] 
    #[trait_gen(U -> u8, u16, u32)]
    ``` 
  - `#[trait_gen(T != U -> u8, u16, u32)]` does the same but only for T != U, so excluding (u8, u8), (u16, u16), and (u32, u32).
    ```rust
    struct Wrapper<T>(T);
    
    // The types T and U must be different to avoid the compilation error
    // "conflicting implementation in crate `core`: impl<T> From<T> for T"
    #[trait_gen(T != U -> u8, u16, u32)]
    impl From<Wrapper<U>> for Wrapper<T> {
        /// converts ${U} to ${T}
        fn from(value: Wrapper<U>) -> Self {
            Wrapper(T::try_from(value.0)
                .expect(&format!("overflow when converting {} to ${T}", value.0)))
        }
    }
    ```
    
  - `#[trait_gen(T < U -> u8, u16, u32)]` generates the code for index(T) < index(U) in the given list, so (T, U) = (u8, u16), (u8, u32), (u16, u32). It's the _position_ in the list that counts; e.g. the types are not sorted (on what criterion would they be sorted anyway?) or checked in any way. 
    ```rust 
    // `From` is only defined for integers with fewer bits (and we exclude a conversion to
    // the same type for the same reason as above)
    #[trait_gen(T < U -> u8, u16, u32)]
    impl From<Wrapper<T>> for Wrapper<U> {
        /// converts Wrapper<${T}> to Wrapper<${U}>
        fn from(value: Wrapper<T>) -> Self {
            Wrapper(U::from(value.0))
        }
    }
    ```

  - `#[trait_gen(T <= U -> u8, u16, u32)]` generates the code for (T, U) = (u8, u8), (u8, u16), (u8, u32), (u16, u16), (u16, u32), (u32, u32)
    ```rust
    // We only want to add integers with fewer bits or of the same type: 
    #[trait_gen(T <= U -> u8, u16, u32)]
    impl Add<Wrapper<T>> for Wrapper<U> {
        type Output = Wrapper<U>;
    
        fn add(self, rhs: Wrapper<T>) -> Self::Output {
            Wrapper::<U>(self.0 + <U>::from(rhs.0))
        }
    }
    ```
- remove the `in` format, which is now strictly reserved to conditionals
- remove the legacy format
- the generic argument must now have the turbofish format if `<..>` is required. Use `#[trait_gen(T::<U> -> ...)` and not `#[trait_gen(T<U> -> ...)`.

# 1.2.1 (2025-05-06)

- fix a bug with the attribute name when the "type_gen" feature is disabled.

# 1.2.0 (2025-05-02)

- add negation in 'trait_gen_if' (the `!` must be in first position after the opening parenthesis):
  ```rust
  use trait_gen::{trait_gen, trait_gen_if}
  
  trait TypeEq<U> {
      fn same_type(&self, other: &U) -> bool;
  }
  
  #[trait_gen(T -> u8, u16, u32)]
  #[trait_gen(U -> u8, u16, u32)]
  impl TypeEq<U> for T {
      #[trait_gen_if(T in U)]
      fn same_type(&self, _other: &U) -> bool {
          true
      }
      #[trait_gen_if(!T in U)]
      fn same_type(&self, _other: &U) -> bool {
          false
      }
  }
  ```
  Note: Attaching an attribute to an expression is still experimental, so we can't simplify the example above, unfortunately.
- `trait_gen_if` and `type_gen_if` must now be declared. I didn't bump the version to 2.x, even if it's technically not back-compatible because of that; the change is minor and so is the current use of this macro. What can I say; I'm flawed.

# 1.1.2 (2025-04-28)

- improve some error messages

# 1.1.1 (2025-04-27)

- fix and simplify doc comment processing
- improve some error messages
- update the minimum stable Rust version to 1.61.0 to comply with syn v2.0.100
- update documentation

# 1.1.0 (2025-04-26)

- add 'trait_gen_if' conditional code inclusion
- add 'type_gen' and 'type_gen_if' synonyms, since the attribute isn't limited to trait implementations
- update documentation

# 1.0.0 (2025-04-24)

- update syn lib to 2.0.100 and fix the [breaking changes](https://github.com/dtolnay/syn/releases/tag/2.0.0) (hopefully)

# 0.3.2 (2023-06-23)

- update documentation

# 0.3.1 (2023-06-02)

- update documentation

# 0.3.0 (2023-05-19)

- move format `#[trait_gen(T in [u64, i64, u32, i32])]` into feature
- add 'deprecated' warnings when using this 'in' format

# 0.2.2 (2023-05-12)

- add alternative format `#[trait_gen(T in [u64, i64, u32, i32])]`

# 0.2.1 (2023-04-11)

- simplify marcro argument processing

# 0.2.0 (2023-03-21)

- add general type substitution:
  ```rust
  #[trait_gen(my::T -> &i32, &mut i32, Box<i32>)]
  impl MyLog for my::T {
      fn my_log2(self) -> u32 {
          MyLog::my_log2(*self)
      }
  }
  ```
- allow substitution in inner `trait_gen` attributes, so that their order doesn't matter:
  ```rust
  #[trait_gen(U -> u8, u16, u32, u64, u128)]
  #[trait_gen(T -> &U, &mut U, Box<U>)]
  impl MyLog for T {
      fn my_log2(self) -> u32 {
          MyLog::my_log2(*self)
      }
  }
  ```

# 0.1.7 (2023-03-07)

- fix bug in multisegment path substitution

# 0.1.6 (2023-03-06)

- add multi-segment paths in parameters:
  ```rust
  #[trait_gen(inner::U -> super::Meter<f32>, super::Foot<f32>)]
  impl Add for inner::U {
      type Output = inner::U;
  
      fn add(self, rhs: Self) -> Self::Output {
          inner::U(self.0 + rhs.0)
      }
  }
  ```
- fix `U::MAX` not replaced with `#[trait_gen(U -> ...)]` and other bugs

# 0.1.5 (2023-03-04)

- add simple type arguments substitution, which can be used in cross-product generation:
  ```rust
  #[trait_gen(T -> Meter, Foot)]
  #[trait_gen(U -> f32, f64)]
  impl GetLength<U> for T<U> {
      fn length(&self) -> U {
          self.0 as U
      }
  }
  ```
- add real type substitution in docs, expression string literals and macros (`${T}`):
  ```rust
  #[trait_gen(T -> u32, u64)]
  impl Lit for T {
      /// Produces a string representation for ${T}
      fn text(&self) -> String {
          call("${T}");
          format!("${T}: {}", self)
      }
  }
  ```

# 0.1.4 (2023-03-01)

- add constructor substitution with the `T ->` form
- all paths starting with the type parameter are replaced, for example `T::default()` has `T` replaced with the `T ->` form (before, the whole path had to match)

# 0.1.3 (2023-02-25)

- add improved attribute format `#[trait_gen(T -> u64, i64, u32, i32)]`
- simplify documentation

# 0.1.2 (2023-02-24)

- fix documentation URL & few typos

# 0.1.1 (2023-02-24)

First version

- trait_gen::trait_gen proc macro