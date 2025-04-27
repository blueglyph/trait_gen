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