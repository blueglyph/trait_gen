mod ex01 {
    use std::ops::Add;
    use typegen::typegen;

    #[derive(Clone, Copy)]
    /// Length in meter
    pub struct Meter(f64);

    #[derive(Clone, Copy)]
    /// Length in meter
    pub struct Foot(f64);

    #[derive(Clone, Copy)]
    /// Length in miles
    pub struct Mile(f64);

    type T = Meter;

    #[typegen(T, Foot, Mile)]
    impl Add for T {
        type Output = T;

        fn add(self, rhs: T) -> Self::Output {
            // The first type identifier, here 'T', must not be redefined by a generic because the
            // macro doesn't handle scopes.
            //
            // Uncomment to test that this is detected and generates an error:
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

    // No occurrence, and usage of `Self` since an alias cannot be used as constructor:
    #[typegen(T, Foot, Mile)]
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

mod ex02 {
    use typegen::typegen;

    pub trait AddMod {
        fn add_mod(self, other: Self, m: Self) -> Self;
    }

    // No need to use `type T = u32` in such a simple case:
    #[typegen(u32, i32, u64, i64, f32, f64)]
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

mod ex03 {
    use typegen::typegen;

    pub trait ToU64 {
        fn into_u64(self) -> u64;
    }
    
    // This will not work:
    //
    // #[typegen(u64, i64, u32, i32, u16, i16, u8, i8)]
    // impl ToU64 for u64 {
    //     fn into_u64(self) -> u64 {
    //         self as u64
    //     }
    // }
    
    type T = u64;
    
    #[typegen(T, i64, u32, i32, u16, i16, u8, i8)]
    impl ToU64 for T {
        /// Transforms the value into a `u64` type
        fn into_u64(self) -> u64 {
            self as u64
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

mod ex04 {
    // This is the equivalent of ex03 when creating a custom declarative macro:

    pub trait ToU64 {
        fn into_u64(self) -> u64;
    }

    macro_rules! impl_to_u64 {
        ($($t:ty)*) => (
            $(impl ToU64 for $t {
                fn into_u64(self) -> u64 {
                    self as u64
                }
            })*
        )
    }

    impl_to_u64! { u64 i64 u32 i32 u16 i16 u8 i8 }

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
