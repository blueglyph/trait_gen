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