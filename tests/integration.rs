// Copyright 2023 Redglyph
//
// Integration tests.

// =============================================================================
// First format:
//
//     // (T needn't be an alias or an existing type)
//     #[trait_gen(T -> Meter, Foot, Mile)]
// or
//     #[trait_gen(Meter -> Meter, Foot, Mile)]
// -----------------------------------------------------------------------------

// Fake types for the tests
struct T { pub offset: u64 }
struct U(u32);

/*
mod subst_cases {
    use trait_gen::trait_gen;

    trait AddMod {
        fn add_mod(self, other: Self, m: Self) -> Self;
    }

    #[trait_gen(U -> u32, i32)]
    impl AddMod for U {
        fn add_mod(self, other: U, m: U) -> U {
            // type must change, constant name must stay:
            const U: U = 0;
            // type must stay:
            let offset: super::U = super::U(0);
            // constant must stay, cast type must change:
            (self + other + U + offset.0 as U) % m
        }
    }

    #[test]
    fn test_add_mod() {
        assert_eq!(10_u32.add_mod(5, 8), 7);
        assert_eq!(10_i32.add_mod(5, 8), 7);
    }
}
*/

mod product_types {
    use std::ops::Add;
    use trait_gen::trait_gen;

    struct Meter<T: Sized>(T);
    struct Foot<T: Sized>(T);

    #[trait_gen(U -> Meter, Foot)]
    #[trait_gen(T -> f32, f64)]
    impl<T> Add for U<T> {
        type Output = U<T>;

        fn add(self, rhs: Self) -> Self::Output {
            U(self.0 + rhs.0)
        }
    }
}

/*
mod ex01a {
    use std::ops::Add;
    use trait_gen::trait_gen;

    #[derive(Clone, Copy)]
    /// Length in meter
    struct Meter(f64);

    #[derive(Clone, Copy)]
    /// Length in meter
    struct Foot(f64);

    #[derive(Clone, Copy)]
    /// Length in miles
    struct Mile(f64);

    // T may be defined as a work-around to get syntactic awareness with the IntelliJ plugin,
    // which doesn't support procedural macros at the moment. With this macro syntax, it
    // doesn't matter whether T is defined or not.
    #[allow(dead_code)]
    type T = Meter;

    #[trait_gen(T -> Meter, Foot, Mile)]
    impl Add for T {
        type Output = T;

        fn add(self, rhs: T) -> Self::Output {
            const T2: f64 = 0.0;
            Self(self.0 + rhs.0 + T2)
        }
    }

    // Usage of `Self(value)` since an alias cannot be used as constructor:
    #[trait_gen(T -> Meter, Foot, Mile)]
    impl Default for T {
        fn default() -> Self {
            Self(0.0)
        }
    }

    #[test]
    fn test_original_type() {
        let a_m = Meter(1.0);
        let b_m = Meter(2.0);
        let c_m = a_m + b_m + Meter::default();
        assert_eq!(c_m.0, 3.0);
    }

    #[test]
    fn test_generated_types() {
        let a_ft = Foot(1.0);
        let b_ft = Foot(2.0);
        let c_ft = a_ft + b_ft + Foot::default();
        assert_eq!(c_ft.0, 3.0);

        let a_mi = Mile(1.0);
        let b_mi = Mile(2.0);
        let c_mi = a_mi + b_mi + Mile::default();
        assert_eq!(c_mi.0, 3.0);
    }
}

mod ex02a {
    use trait_gen::trait_gen;

    trait AddMod {
        fn add_mod(self, other: Self, m: Self) -> Self;
    }

    // No need to use `type T = u32` in such a simple case:
    #[trait_gen(u32 -> u32, i32, u64, i64, f32, f64)]
    impl AddMod for u32 {
        fn add_mod(self, other: Self, m: Self) -> Self {
            (self + other) % m
        }
    }

    #[test]
    fn test_add_mod() {
        assert_eq!(10_u32.add_mod(5, 8), 7);
        assert_eq!(10_i32.add_mod(5, 8), 7);
        assert_eq!(10_u64.add_mod(5, 8), 7);
        assert_eq!(10_i64.add_mod(5, 8), 7);
        assert_eq!(10_f32.add_mod(5.0, 8.0), 7.0);
        assert_eq!(10_f64.add_mod(5.0, 8.0), 7.0);
    }
}

mod ex03a {
    use trait_gen::trait_gen;

    trait ToU64 {
        fn into_u64(self) -> u64;
    }

    #[trait_gen(T -> u64, i64, u32, i32, u16, i16, u8, i8)]
    impl ToU64 for T {
        /// Transforms the value into a `u64` type
        fn into_u64(self) -> u64 {
            // Type paths with a 'T' segment are fine, they won't be substituted:
            let x: super::T = super::T { offset: 0 };

            // Constant names with the same name as the substituted type are fine:
            // (same for variable and functions, though they shouldn't have the same case)
            const T2: u64 = 0;

            self as u64 + T2 + x.offset
        }
    }

    #[test]
    fn test() {
        let a = 10_u64;
        let b = 10_i64;
        let c = 10_u32;
        let d = 10_i32;
        let e = 10_u16;
        let f = 10_i16;
        let g = 10_u8;
        let h = 10_i8;

        assert_eq!(a.into_u64(), 10_u64);
        assert_eq!(b.into_u64(), 10_u64);
        assert_eq!(c.into_u64(), 10_u64);
        assert_eq!(d.into_u64(), 10_u64);
        assert_eq!(e.into_u64(), 10_u64);
        assert_eq!(f.into_u64(), 10_u64);
        assert_eq!(g.into_u64(), 10_u64);
        assert_eq!(h.into_u64(), 10_u64);
    }
}

// =============================================================================
// Second "legacy" format:
//
//     type T = Meter;
//     #[trait_gen(T, Foot, Mile)]
// or
//     #[trait_gen(Meter, Foot, Mile)]
// -----------------------------------------------------------------------------

mod ex01b {
    use std::ops::Add;
    use trait_gen::trait_gen;

    #[derive(Clone, Copy)]
    /// Length in meter
    struct Meter(f64);

    #[derive(Clone, Copy)]
    /// Length in meter
    struct Foot(f64);

    #[derive(Clone, Copy)]
    /// Length in miles
    struct Mile(f64);

    type T = Meter;

    #[trait_gen(T, Foot, Mile)]
    impl Add for T {
        type Output = T;

        fn add(self, rhs: T) -> Self::Output {
            // The first type identifier, here 'T', must not be redefined by a generic because the
            // macro doesn't handle scopes.
            //
            // Uncomment the code below to see the error:
            // --------------------------------
            // fn fake<T: Sized>(_x: T) {
            //     println!("x-x");
            // }
            // fake(1_u32);
            // --------------------------------

            let _zero = T::default();

            // Note that it is not possible to use a type alias to instantiate an object, so here
            // we use `Self( ... )` and not `T( ... )`. The intermediate `result` variable is
            // optional and is only there to test the type substitution:

            let result: T = Self(self.0 + rhs.0);
            result
        }
    }

    // Usage of `Self(value)` since an alias cannot be used as constructor:
    #[trait_gen(T, Foot, Mile)]
    impl Default for T {
        fn default() -> Self {
            Self(0.0)
        }
    }

    #[test]
    fn test_original_type() {
        let a_m = Meter(1.0);
        let b_m = Meter(2.0);
        let c_m = a_m + b_m + Meter::default();
        assert_eq!(c_m.0, 3.0);
    }

    #[test]
    fn test_generated_types() {
        let a_ft = Foot(1.0);
        let b_ft = Foot(2.0);
        let c_ft = a_ft + b_ft + Foot::default();
        assert_eq!(c_ft.0, 3.0);

        let a_mi = Mile(1.0);
        let b_mi = Mile(2.0);
        let c_mi = a_mi + b_mi + Mile::default();
        assert_eq!(c_mi.0, 3.0);
    }
}

mod ex02b {
    use trait_gen::trait_gen;

    trait AddMod {
        fn add_mod(self, other: Self, m: Self) -> Self;
    }

    // No need to use `type T = u32` in such a simple case:
    #[trait_gen(u32, i32, u64, i64, f32, f64)]
    impl AddMod for u32 {
        fn add_mod(self, other: Self, m: Self) -> Self {
            (self + other) % m
        }
    }

    #[test]
    fn test_add_mod() {
        assert_eq!(10_u32.add_mod(5, 8), 7);
        assert_eq!(10_i32.add_mod(5, 8), 7);
        assert_eq!(10_u64.add_mod(5, 8), 7);
        assert_eq!(10_i64.add_mod(5, 8), 7);
        assert_eq!(10_f32.add_mod(5.0, 8.0), 7.0);
        assert_eq!(10_f64.add_mod(5.0, 8.0), 7.0);
    }
}

mod ex03b {
    use trait_gen::trait_gen;

    trait ToU64 {
        fn into_u64(self) -> u64;
    }
    
    // This doesn't work because the 'u64' return type of 'into_u64' would be substituted too:
    //
    // #[trait_gen(u64, i64, u32, i32, u16, i16, u8, i8)]
    // impl ToU64 for u64 {
    //     fn into_u64(self) -> u64 {
    //         self as u64
    //     }
    // }

    type T = u64;
    
    #[trait_gen(T, i64, u32, i32, u16, i16, u8, i8)]
    impl ToU64 for T {
        /// Transforms the value into a `u64` type
        fn into_u64(self) -> u64 {
            // Type paths with a 'T' segment are fine, they won't be substituted:
            let x: super::T = super::T { offset: 0 };

            // Constant names with the same name as the substituted type are fine:
            // (same for variable and functions, though they shouldn't have the same case)
            const T: u64 = 0;

            self as u64 + T + x.offset
        }
    }
    
    #[test]
    fn test() {
        let a = 10_u64;
        let b = 10_i64;
        let c = 10_u32;
        let d = 10_i32;
        let e = 10_u16;
        let f = 10_i16;
        let g = 10_u8;
        let h = 10_i8;
    
        assert_eq!(a.into_u64(), 10_u64);
        assert_eq!(b.into_u64(), 10_u64);
        assert_eq!(c.into_u64(), 10_u64);
        assert_eq!(d.into_u64(), 10_u64);
        assert_eq!(e.into_u64(), 10_u64);
        assert_eq!(f.into_u64(), 10_u64);
        assert_eq!(g.into_u64(), 10_u64);
        assert_eq!(h.into_u64(), 10_u64);
    }    
}

*/