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

mod type_cases_01 {
    use trait_gen::trait_gen;

    trait MyLog {
        fn my_log2(self) -> u32;
    }

    impl MyLog for i32 {
        fn my_log2(self) -> u32 {
            i32::BITS - 1 -self.leading_zeros()
        }
    }

    #[trait_gen(my::T -> &i32, &mut i32, Box<i32>)]
    impl MyLog for my::T {
        fn my_log2(self) -> u32 {
            MyLog::my_log2(*self)
        }
    }

    fn show_log2(x: impl MyLog) -> u32 {
        x.my_log2()
    }

    #[test]
    fn test() {
        let a = 6;
        let p_a = &a;
        let mut b = 1023;
        let p_b = &mut b;
        let box_a = Box::new(a);

        assert_eq!(show_log2(a), 2);
        assert_eq!(show_log2(p_a), 2);
        assert_eq!(show_log2(p_b), 9);
        assert_eq!(show_log2(box_a), 2);
    }
}

mod type_cases_02 {
    use trait_gen::trait_gen;

    trait MyLog {
        fn my_log2(self) -> u32;
    }

    #[trait_gen(T -> u8, u16, u32, u64, u128)]
    impl MyLog for T {
        fn my_log2(self) -> u32 {
            T::BITS - 1 -self.leading_zeros()
        }
    }

    // The order of the attributes doesn't matter:
    #[trait_gen(U -> u8, u16, u32, u64, u128)]
    #[trait_gen(T -> &U, &mut U, Box<U>)]
    impl MyLog for T {
        fn my_log2(self) -> u32 {
            MyLog::my_log2(*self)
        }
    }

    fn show_log2(x: impl MyLog) -> u32 {
        x.my_log2()
    }

    #[test]
    fn test() {
        let a = 6_u32;
        let p_a = &a;
        let mut b = 1023_u64;
        let p_b = &mut b;
        let box_a = Box::new(a);

        assert_eq!(show_log2(a), 2);
        assert_eq!(show_log2(p_a), 2);
        assert_eq!(show_log2(p_b), 9);
        assert_eq!(show_log2(box_a), 2);
    }
}

mod type_cases_03 {
    use trait_gen::trait_gen;

    trait Name {
        fn name(&self) -> String;
    }

    #[trait_gen(my::U -> i8, u8, i16, u16, i32, u32, i64, u64, i128, u128)]
    #[trait_gen(my::T -> &[my::U; N], &mut [my::U; N], Box<[my::U; N]>)]
    impl<const N: usize> Name for my::T {
        fn name(&self) -> String {
            format!("slice of ${my::T} with N = {}", N)
        }
    }

    fn show_name(value: &impl Name) -> String {
        value.name()
    }

    #[test]
    fn test() {
        let a = &[10, 20];
        let b = &mut [10_u32, 15, 20];
        let c = Box::new([5_u64, 6, 7, 8]);

        assert_eq!(a.name(), "slice of &[i32;N] with N = 2");
        assert_eq!(b.name(), "slice of &mut [u32;N] with N = 3");
        assert_eq!(c.name(), "slice of Box::<[u64;N]> with N = 4");

        assert_eq!(show_name(&a), "slice of &[i32;N] with N = 2");
        assert_eq!(show_name(&b), "slice of &mut [u32;N] with N = 3");
        assert_eq!(show_name(&c), "slice of Box::<[u64;N]> with N = 4");
    }
}

mod type_cases_04 {
    use trait_gen::trait_gen;

    #[derive(Debug, PartialEq)]
    struct Meter(i64);
    #[derive(Debug, PartialEq)]
    struct Foot(i64);

    trait Negate {
        type Output;
        fn negate(self) -> Self::Output;
    }

    #[trait_gen(T -> Meter, Foot)]
    impl Negate for T {
        type Output = T;
        fn negate(self) -> Self::Output {
            T(-self.0)
        }
    }

    #[trait_gen(U -> &T, &mut T, Box<T>)]
    #[trait_gen(T -> Meter, Foot)]
    impl Negate for U {
        type Output = T;
        fn negate(self) -> Self::Output {
            T(-self.deref().0)
        }
    }

    fn negate<T, O>(x: T) -> O
        where T: Negate<Output = O>
    {
        x.negate()
    }

    #[test]
    fn test() {
        let x: Meter = Meter(5);
        let x_ref: &Meter = &Meter(5);
        let y = negate(x);
        let y_ref = negate(x_ref);
        assert_eq!(y, Meter(-5));  // doesn't need forward definition
        assert_eq!(y_ref, Meter(-5));
    }

}

// Fake types for the tests
struct T { pub offset: u64 }
struct U(u32);
struct Meter<T>(T);
struct Foot<T>(T);

mod path_cases_01 {
    use trait_gen::trait_gen;
    use std::ops::{Add, Neg};

    pub mod inner {}

    #[trait_gen(U -> super::Meter<f32>, super::Foot<f32>)]
    impl Add for U {
        type Output = U;

        fn add(self, rhs: Self) -> Self::Output {
            U(self.0 + rhs.0)
        }
    }

    #[trait_gen(super::Meter<f32>, super::Foot<f32>)]
    impl Neg for super::Meter<f32> {
        type Output = super::Meter<f32>;

        fn neg(self) -> Self::Output {
            super::Meter::<f32>(-self.0)
        }
    }

    #[test]
    fn test() {
        let a = super::Meter::<f32>(1.0);
        let b = super::Meter::<f32>(4.0);

        let c = a + b;
        assert_eq!(c.0, 5.0);
        let d = -c;
        assert_eq!(d.0, -5.0);

        let a = super::Foot::<f32>(1.0);
        let b = super::Foot::<f32>(4.0);

        let c = a + b;
        assert_eq!(c.0, 5.0);
        let d = -c;
        assert_eq!(d.0, -5.0);
    }
}

mod path_cases_02 {

    struct Meter<T>(T);
    struct Foot<T>(T);

    pub mod inner {
        use trait_gen::trait_gen;
        use std::ops::Add;
        
        #[trait_gen(gen::U -> super::Meter<f32>, super::Foot<f32>)]
        impl Add for gen::U {
            type Output = gen::U;
        
            fn add(self, rhs: Self) -> Self::Output {
                gen::U(self.0 + rhs.0)
            }
        }
        
        #[test]
        fn test() {
            let a = super::Meter::<f32>(1.0);
            let b = super::Meter::<f32>(4.0);
        
            let c = a + b;
            assert_eq!(c.0, 5.0);
        
            let a = super::Foot::<f32>(1.0);
            let b = super::Foot::<f32>(4.0);
        
            let c = a + b;
            assert_eq!(c.0, 5.0);
        }
    }
}

mod path_cases_03 {
    use trait_gen::trait_gen;
    use std::fmt::Display;

    struct Name<'a>(&'a str);
    struct Value(i32);
    struct AnyValue<T: Display>(T);
    struct AnyData<T: Display>(T);

    trait Show {
        fn show(&self) -> String;
    }

    #[trait_gen(T -> Name<'_>, Value)]
    impl Show for T {
        fn show(&self) -> String {
            self.0.to_string()
        }
    }

    // this would be easier, but testing the more complicated case to illustrate
    // how to avoid collisions, and to test a blanket implementation:
    //     #[trait_gen(T -> AnyValue, AnyData)]
    //     impl<U: Display> Show for T<U> {
    #[trait_gen(T -> AnyValue<U>, AnyData<U>)]
    impl<U: Display> Show for T {
        fn show(&self) -> String {
            self.0.to_string()
        }
    }

    #[test]
    fn test() {
        assert_eq!(Name("Bob").show(), "Bob");
        assert_eq!(Value(10).show(), "10");
        assert_eq!(AnyValue(5.0).show(), "5");
        assert_eq!(AnyData("name".to_string()).show(), "name");
    }
}

mod path_cases_04 {
    use trait_gen::trait_gen;

    struct Name<'a>(&'a str);
    struct Value<'a>(&'a f64);

    trait Show {
        fn show(&self) -> String;
    }

    #[trait_gen(T -> Name, Value)]
    impl Show for T<'_> {
        fn show(&self) -> String {
            self.0.to_string()
        }
    }

    #[test]
    fn test() {
        assert_eq!(Name("Bob").show(), "Bob");
        assert_eq!(Value(&10.0).show(), "10");
    }
}

mod path_cases_05 {
    struct Name<'a>(&'a str);
    struct Value<'a>(&'a f64);
    mod inner {
        mod depth {
            use trait_gen::trait_gen;

            trait Show {
                fn show(&self) -> String;
            }

            #[trait_gen(T -> super::super::Name, super::super::Value)]
            impl Show for T<'_> {
                fn show(&self) -> String {
                    self.0.to_string()
                }
            }

            #[test]
            fn test() {
                assert_eq!(super::super::Name("Bob").show(), "Bob");
                assert_eq!(super::super::Value(&10.0).show(), "10");
            }
        }
    }
}

mod path_cases_06 {
    use trait_gen::trait_gen;

    struct Name<'a>(&'a str);
    struct Value<'a>(&'a f64);

    trait Show {
        fn show(&self) -> String;
    }

    #[trait_gen(gen::par -> Name, Value)]
    impl Show for gen::par<'_> {
        fn show(&self) -> String {
            self.0.to_string()
        }
    }

    #[test]
    fn test() {
        assert_eq!(Name("Bob").show(), "Bob");
        assert_eq!(Value(&10.0).show(), "10");
    }
}

mod literals {
    use trait_gen::trait_gen;
    static mut CALLS: Vec<String> = Vec::new();

    trait Lit {
        fn text(&self) -> String;
    }

    fn call(s: &str) {
        unsafe { CALLS.push(s.to_string()); }
    }

    #[trait_gen(T -> u32, u64)]
    impl Lit for T {
        /// Produces a string representation for ${T}
        fn text(&self) -> String {
            call("${T}");
            format!("${T}: {}", self)
        }
    }

    #[test]
    fn test() {
        let s_32 = 10_u32.text();
        let s_64 = 20_u64.text();
        assert_eq!(s_32, "u32: 10");
        assert_eq!(s_64, "u64: 20");
        assert_eq!(unsafe { CALLS.join(",") }, "u32,u64");
    }
}

mod subst_cases {
    use std::ops::{Add, Sub};
    use trait_gen::trait_gen;

    trait AddMod {
        fn add_mod(self, other: Self, m: Self) -> Self;
    }

    #[trait_gen(U -> u32, i32)]
    impl AddMod for U {
        fn add_mod(self, other: U, m: U) -> U {
            // constant name must stay, type must change:
            const U: U = 0;
            // U:: type must change, U.add(U) must stay:
            let zero1 = U::default() + U.add(U);
            let zero2 = U::MAX.sub(U::MAX);
            // type must stay:
            let offset: super::U = super::U(0);
            // constant must stay, cast type must change:
            (self + other + U + zero1 + zero2 + offset.0 as U) % m
        }
    }

    #[test]
    fn test_add_mod() {
        assert_eq!(10_u32.add_mod(5, 8), 7);
        assert_eq!(10_i32.add_mod(5, 8), 7);
    }
}

mod type_args {
    use trait_gen::trait_gen;

    trait Number<X, T> { fn fake(x: X) -> T; }

    #[trait_gen(T -> f32, f64)]
    // all trait arguments must change:
    impl Number<T, T> for T {
        /// my fake doc
        fn fake(_x: T) -> T { 1.0 as T }
    }

    struct Meter<U>(U);

    trait GetLength<T> {
        fn length(&self) -> T;
    }

    #[trait_gen(U -> f32, f64)]
    impl GetLength<U> for Meter<U> {
        #[doc = "length for type `Meter<${U}>`"]
        fn length(&self) -> U {
            // generic ident must not collide, but bound arguments must change:
            fn identity<T: Number<U, U>>(x: T) -> T { x }
            identity(self.0 as U)
        }
    }

    #[test]
    fn test() {
        let m_32 = Meter(1.0_f32);
        let m_64 = Meter(2.0);
        assert_eq!(m_32.length(), 1.0_f32);
        assert_eq!(m_64.length(), 2.0_f64);
    }
}

mod type_fn_args {
    use trait_gen::trait_gen;

    trait Transformer<T: Copy> {
        fn transform<F: Fn(T) -> T>(&self, f: F) -> Vec<T>;
    }

    #[trait_gen(T -> i64, f64)]
    impl Transformer<T> for Vec<T> {
        fn transform<F: Fn(T) -> T>(&self, f: F) -> Vec<T> {
            self.iter().map(|&x| f(x)).collect()
        }
    }

    #[test]
    fn test() {
        let vi = vec![1_i64, 2, 3, 4, 5];
        let vf = vec![1.0_f64, 4.0, 9.0, 16.0, 25.0];
        let transformed_vi = vi.transform(|x| x * x);
        let transformed_vf = vf.transform(|x| x.sqrt());
        assert_eq!(transformed_vi, [1, 4, 9, 16, 25]);
        assert_eq!(transformed_vf, [1.0, 2.0, 3.0, 4.0, 5.0]);
    }
}

mod cross_product {
    use trait_gen::trait_gen;

    struct Meter<U>(U);
    struct Foot<U>(U);

    trait GetLength<T> {
        fn length(&self) -> T;
    }

    // #[trait_gen(T -> Meter, Foot)]
    // #[trait_gen(U -> f32, f64)]
    // impl GetLength<U> for T<U> {
    //     fn length(&self) -> U {
    //         self.0 as U
    //     }
    // }

    // Warning! The substitution is not done in attribute paramters. If parameters of attribute A
    //          include the generic parameter of another attribute B, A should be put first. It will
    //          copy its parameters literally, and they will be replaced when B is processed:
    //
    #[trait_gen(T -> Meter<U>, Foot<U>)]    // <-- attribute A, parameters include generic 'U' of B
    #[trait_gen(U -> f32, f64)]             // <-- attribute B
    impl GetLength<U> for T {
        fn length(&self) -> U {
            self.0 as U
        }
    }

    #[test]
    fn test() {
        let m_32 = Meter(1.0_f32);
        let m_64 = Meter(2.0);
        let f_32 = Foot(3.0_f32);
        let f_64 = Foot(4.0);
        assert_eq!(m_32.length(), 1.0_f32);
        assert_eq!(m_64.length(), 2.0_f64);
        assert_eq!(f_32.length(), 3.0_f32);
        assert_eq!(f_64.length(), 4.0_f64);
    }
}

mod ex01a {
    use std::ops::Add;
    use trait_gen::trait_gen;

    #[derive(Clone, Copy)]
    /// Length in meter
    struct Meter(f64);

    #[derive(Clone, Copy)]
    /// Length in foot
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
            const T: f64 = 0.0;
            // constructor must change:
            T(self.0 + rhs.0 + T)
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
            // type and constructor must not change because it doesn't start with 'T':
            let x: super::T = super::T { offset: 0 };
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
    /// Length in foot
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
