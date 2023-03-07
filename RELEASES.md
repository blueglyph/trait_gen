# 0.1.7 (2023-03-07)

- fix bug in multisegment path substitution

# 0.1.6 (2023-03-06)

- add multi-segment paths in parameters
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