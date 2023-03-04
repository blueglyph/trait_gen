# 0.1.5 (2023-03-04)

- attribute type parameter can be used in simple type arguments, which can be used in cross-product generation:
    ```rust
    #[trait_gen(T -> Meter, Foot)]
    #[trait_gen(U -> f32, f64)]
    impl GetLength<U> for T<U> {
        fn length(&self) -> U {
            self.0 as U
        }
    }
    ```
- substitutes the real type for `${T}` in docs, expression string literals and macros:
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

- attribute type parameter can be used as constructor with the `T ->` form
- all paths starting with the type parameter are replaced, for example `T::default()` has `T` replaced with the `T ->` form (before, the whole path had to match)

# 0.1.3 (2023-02-25)

- add improved attribute format `#[trait_gen(T -> u64, i64, u32, i32)]`
- simplify documentation

# 0.1.2 (2023-02-24)

- fix documentation URL & few typos

# 0.1.1 (2023-02-24)

First version

- trait_gen::trait_gen proc macro