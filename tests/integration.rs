// Copyright 2023 Redglyph
//
// Integration tests.

/// Tests the `#[trait_gen(T -> i16, u16)]` format
mod simple_formats {
    use trait_gen::trait_gen;

    struct Test<T>(T);

    // main format
    #[trait_gen(T -> i16, u16)]
    impl Test<T> {
        fn test() -> bool { true }
    }

    // verifies that brackets can be used for types with the '->' syntax
    #[trait_gen(T -> [i64;2])]
    impl Test<T> {
        fn test() -> bool { true }
    }

    #[trait_gen(T -> &[u64])]
    impl Test<T> {
        fn test() -> bool { true }
    }

    #[trait_gen(T -> (u32, u32), (u8, u8))]
    impl Test<T> {
        #[allow(unused)]
        fn test() -> bool { true }
    }

    #[test]
    fn test() {
        assert!(Test::<i16>::test());
        assert!(Test::<u16>::test());
        assert!(Test::<[i64;2]>::test());
        assert!(Test::<&[u64]>::test());
        assert!(Test::<(u32, u32)>::test());
    }
}

/// Tests the `#[trait_gen(A, B -> u8, u16)]` format
mod advanced_format_all {
    use std::ops::Add;
    use trait_gen::{trait_gen};

    #[derive(PartialEq, Debug)]
    struct Wrapper<T>(T);

    #[trait_gen(A, B -> u8, u16)]
    impl Add<Wrapper<B>> for Wrapper<A> {
        type Output = Wrapper<A>;

        fn add(self, rhs: Wrapper<B>) -> Self::Output {
            Wrapper::<A>(self.0 + A::try_from(rhs.0).expect(&format!("overflow when converting {} to ${A}", rhs.0)))
        }
    }

    #[test]
    fn test() {
        assert_eq!(Wrapper(1_u8) + Wrapper(2_u8), Wrapper(3_u8));
        assert_eq!(Wrapper(1_u8) + Wrapper(2_u16), Wrapper(3_u8));
        assert_eq!(Wrapper(1_u16) + Wrapper(2_u8), Wrapper(3_u16));
        assert_eq!(Wrapper(1_u16) + Wrapper(2_u16), Wrapper(3_u16));
    }

    #[test]
    #[should_panic]
    fn test_fail() {
        let x = Wrapper(1_u8) + Wrapper(1000_u16);
        println!("{x:?}");
    }
}

/// Tests the `#[trait_gen(T != U -> u8, u16, u32)]` format
mod advanced_format_diff {
    use trait_gen::trait_gen;

    #[derive(Clone, PartialEq, Debug)]
    struct Wrapper<T>(T);

    // The type must be different to avoid the error "conflicting implementation in crate `core`: impl<T> From<T> for T"
    #[trait_gen(T != U -> u8, u16, u32)]
    impl From<Wrapper<U>> for Wrapper<T> {
        /// converts ${U} to ${T}
        fn from(value: Wrapper<U>) -> Self {
            Wrapper(T::try_from(value.0).expect(&format!("overflow when converting {} to ${T}", value.0)))
        }
    }

    #[test]
    fn test() {
        // other combinations would trigger the "conflicting implementation" error,
        // so no need to explicitly test they're not implemented
        assert_eq!(Wrapper::<u8>::from(Wrapper(10_u8)), Wrapper(10_u8));
        assert_eq!(Wrapper::<u16>::from(Wrapper(10_u8)), Wrapper(10_u16));
        assert_eq!(Wrapper::<u32>::from(Wrapper(10_u8)), Wrapper(10_u32));
        assert_eq!(Wrapper::<u8>::from(Wrapper(20_u16)), Wrapper(20_u8));
        assert_eq!(Wrapper::<u16>::from(Wrapper(20_u16)), Wrapper(20_u16));
        assert_eq!(Wrapper::<u32>::from(Wrapper(20_u16)), Wrapper(20_u32));
        assert_eq!(Wrapper::<u8>::from(Wrapper(30_u32)), Wrapper(30_u8));
        assert_eq!(Wrapper::<u16>::from(Wrapper(30_u32)), Wrapper(30_u16));
        assert_eq!(Wrapper::<u32>::from(Wrapper(30_u32)), Wrapper(30_u32));
    }
}

/// Tests the `#[trait_gen(T !< U -> u8, u16, u32)]` format
mod advanced_format_exclusive {
    use trait_gen::trait_gen;

    #[derive(Clone, PartialEq, Debug)]
    struct Wrapper<T>(T);

    // The type must be different to avoid the error "conflicting implementation in crate `core`: impl<T> From<T> for T"
    #[trait_gen(T !< U -> u8, u16, u32)]
    impl From<Wrapper<T>> for Wrapper<U> {
        /// converts ${T} to ${U}
        fn from(value: Wrapper<T>) -> Self {
            Wrapper(U::from(value.0))
        }
    }

    #[test]
    fn test() {
        // other combinations would trigger the "conflicting implementation" or
        // "trait `From<u16>` is not implemented for `u8`" error,
        // so no need to explicitly test they're not implemented
        assert_eq!(Wrapper::<u16>::from(Wrapper(10_u8)), Wrapper(10_u16));
        assert_eq!(Wrapper::<u32>::from(Wrapper(10_u8)), Wrapper(10_u32));
        assert_eq!(Wrapper::<u32>::from(Wrapper(20_u16)), Wrapper(20_u32));
    }
}

/// Tests the `#[trait_gen(T =< U -> u8, u16, u32)]` format
mod advanced_format_inclusive {
    use std::ops::Add;
    use trait_gen::trait_gen;

    #[derive(PartialEq, Debug)]
    struct Wrapper<T>(T);

    #[trait_gen(T =< U -> u8, u16, u32)]
    impl Add<Wrapper<T>> for Wrapper<U> {
        type Output = Wrapper<U>;

        fn add(self, rhs: Wrapper<T>) -> Self::Output {
            Wrapper::<U>(self.0 + <U>::from(rhs.0))
        }
    }

    #[test]
    fn test() {
        // other combinations would trigger the "trait `From<u16>` is not implemented for `u8`"
        // error, so no need to explicitly test they're not implemented
        assert_eq!(Wrapper(1_u8) + Wrapper(10_u8), Wrapper(11_u8));
        assert_eq!(Wrapper(1_u16) + Wrapper(10_u8), Wrapper(11_u16));
        assert_eq!(Wrapper(1_u32) + Wrapper(10_u8), Wrapper(11_u32));
        assert_eq!(Wrapper(1_u16) + Wrapper(10_u16), Wrapper(11_u16));
        assert_eq!(Wrapper(1_u32) + Wrapper(10_u16), Wrapper(11_u32));
        assert_eq!(Wrapper(1_u32) + Wrapper(10_u32), Wrapper(11_u32));
    }
}

/// Tests the attribute without declaring it in a `use`
mod no_use_example {
    #[derive(Clone, PartialEq, Debug)]
    struct Wrapper<T>(T);

    #[trait_gen::trait_gen(T -> u8, u16, u32)]
    #[trait_gen::trait_gen_if(!T in u8)]
    impl From<Wrapper<u8>> for Wrapper<T> {
        fn from(value: Wrapper<u8>) -> Self {
            Wrapper(T::from(value.0))
        }
    }

    #[test]
    fn test() {
        let a = Wrapper(10_u8);
        assert_eq!(Wrapper::<u8>::from(a.clone()), Wrapper(10_u8));
        assert_eq!(Wrapper::<u16>::from(a.clone()), Wrapper(10_u16));
        assert_eq!(Wrapper::<u32>::from(a), Wrapper(10_u32));
    }
}

/// Tests the `#[trait_gen_if(T in Metre)]` conditional attribute with one item
mod conditional_code {
    use std::ops::Add;
    use trait_gen::{trait_gen, trait_gen_if};

    #[derive(Clone, Copy, Debug, PartialEq)]
    struct Metre(f64);
    #[derive(Clone, Copy, Debug, PartialEq)]
    struct Foot(f64);
    // to do:
    // struct QuarterPounderWithCheese(u32);
    // struct RoyaleWithCheese(u32);

    trait Metrics {
        const TO_METRE: f64;
        fn to_metre(&self) -> f64;
    }

    #[trait_gen(T -> Metre, Foot)]
    impl Metrics for T {
        #[trait_gen_if(T in Metre)]
        const TO_METRE: f64 = 1.0;
        #[trait_gen_if(T in Foot)]
        const TO_METRE: f64 = 0.3048;

        fn to_metre(&self) -> f64 {
            self.0 * Self::TO_METRE
        }
    }

    #[trait_gen(A -> Metre, Foot)]
    #[trait_gen(B -> Metre, Foot)]
    impl Add<B> for A {
        type Output = A;

        fn add(self, rhs: B) -> Self::Output {
            A((self.to_metre() + rhs.to_metre())/Self::TO_METRE)
        }
    }

    #[test]
    fn test() {
        let a = Metre(1.0);
        let b = Metre(3.048);
        let c = Foot(20.0);
        let d = Foot(25.0);

        let a_b = a + b;
        let a_c = a + c;
        let c_d = c + d;
        let c_b = c + b;

        assert_eq!(a_b, Metre(4.048));
        assert_eq!(a_c, Metre(7.096));
        assert_eq!(c_d, Foot(45.0));
        assert_eq!(c_b, Foot(30.0))
    }
}

/// Tests the `#[trait_gen_if(T in i8, u8)]` conditional attribute with several items
mod conditional_code2 {
    use trait_gen::{trait_gen, trait_gen_if};

    trait Binary {
        const DECIMAL_DIGITS: usize;
        const SIGN: bool = false;
        fn display_length() -> usize;
        fn try_neg(self) -> Option<Self> where Self: Sized { None }
    }
    
    #[trait_gen(T -> i8, u8, i32, u32)]
    impl Binary for T {
        #[trait_gen_if(T in i8, u8)]
        const DECIMAL_DIGITS: usize = 3;
        #[trait_gen_if(T in i32, u32)]
        const DECIMAL_DIGITS: usize = 10;
        #[trait_gen_if(T in i8, i32)]
        const SIGN: bool = true;
     
        fn display_length() -> usize {
            Self::DECIMAL_DIGITS + if T::SIGN { 1 } else { 0 }
        }
    
        #[trait_gen_if(T in i8, i32)]
        fn try_neg(self) -> Option<Self> {
            Some(-self)
        }
    }

    #[test]
    fn test() {
        assert_eq!(10_i8.try_neg(), Some(-10));
        assert_eq!(20_u8.try_neg(), None);
        assert_eq!(30_i32.try_neg(), Some(-30));
        assert_eq!(40_u32.try_neg(), None);
        assert_eq!(i8::display_length(), 4);
        assert_eq!(u8::display_length(), 3);
        assert_eq!(i32::display_length(), 11);
        assert_eq!(u32::display_length(), 10);
    }
}

/// Tests the `#[trait_gen_if(!T in U)]` conditional attribute with a negation
mod conditional_code3 {
    use trait_gen::{trait_gen, trait_gen_if};
    
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

    #[test]
    fn test() {
        let a = 10_u8;
        let b = 20_u16;
        let c = 30_u32;
        assert_eq!(a.same_type(&b), false, "a.same_type(&b) failed");
        assert_eq!(a.same_type(&c), false, "a.same_type(&c) failed");
        assert_eq!(b.same_type(&a), false, "b.same_type(&a) failed");
        assert_eq!(b.same_type(&c), false, "b.same_type(&c) failed");
        assert_eq!(c.same_type(&a), false, "c.same_type(&a) failed");
        assert_eq!(c.same_type(&b), false, "c.same_type(&b) failed");
        assert_eq!(a.same_type(&a), true, "a.same_type(&a) failed");
        assert_eq!(b.same_type(&b), true, "b.same_type(&b) failed");
        assert_eq!(c.same_type(&c), true, "c.same_type(&c) failed");
    }
}

mod type_case_01 {
    use trait_gen::trait_gen;

    trait MyLog {
        fn my_log2(self) -> u32;
    }

    impl MyLog for i32 {
        fn my_log2(self) -> u32 {
            i32::BITS - 1 - self.leading_zeros()
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

mod type_case_02 {
    use trait_gen::trait_gen;

    trait MyLog {
        fn my_log2(self) -> u32;
    }

    #[trait_gen(T -> u8, u16, u32, u64, u128)]
    impl MyLog for T {
        fn my_log2(self) -> u32 {

            T::BITS - 1 - self.leading_zeros()
        }
    }

    // The order of the attributes doesn't matter:
    #[trait_gen(T -> u8, u16, u32, u64, u128)]
    #[trait_gen(U -> &T, &mut T, Box<T>)]
    impl MyLog for U {
        /// Logarithm base 2 for `${U}`
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
        assert_eq!(show_log2(box_a.clone()), 2);

        assert_eq!(a.my_log2(), 2);
        assert_eq!((&a).my_log2(), 2);
        assert_eq!((&mut b).my_log2(), 9);
        assert_eq!(box_a.my_log2(), 2);
    }
}

mod type_case_03 {
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

mod type_case_04 {
    use std::ops::Deref;
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
            #[allow(suspicious_double_ref_op)] // to fix with conditional?
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

mod path_case_01 {
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

    #[trait_gen(U -> super::Meter<f32>, super::Foot<f32>)]
    impl Neg for U {
        type Output = U;

        fn neg(self) -> Self::Output {
            U(-self.0)
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

mod path_case_02 {
    struct Meter<T>(T);
    struct Foot<T>(T);

    pub mod inner {
        use trait_gen::trait_gen;
        use std::ops::Add;
        
        #[trait_gen(g::U -> super::Meter<f32>, super::Foot<f32>)]
        impl Add for g::U {
            type Output = g::U;
        
            fn add(self, rhs: Self) -> Self::Output {
                g::U(self.0 + rhs.0)
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

mod path_case_03 {
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

mod path_case_04 {
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

mod path_case_05 {
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

mod path_case_06 {
    use trait_gen::trait_gen;

    struct Name<'a>(&'a str);
    struct Value<'a>(&'a f64);

    trait Show {
        fn show(&self) -> String;
    }

    #[trait_gen(g::par -> Name, Value)]
    impl Show for g::par<'_> {
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

    trait Lit {
        fn text(&self, calls: &mut Vec<String>) -> String;
    }

    fn call(calls: &mut Vec<String>, s: &str) {
        calls.push(s.to_string());
    }

    #[trait_gen(T -> u32, u64)]
    impl Lit for T {
        /// Produces a string representation for ${T}
        fn text(&self, calls: &mut Vec<String>) -> String {
            call(calls, "${T}");
            format!("${T}: {}", self)
        }
    }

    #[test]
    fn test() {
        let mut calls = Vec::<String>::new();
        let s_32 = 10_u32.text(&mut calls);
        let s_64 = 20_u64.text(&mut calls);
        assert_eq!(s_32, "u32: 10");
        assert_eq!(s_64, "u64: 20");
        assert_eq!(calls.join(","), "u32,u64");
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

    trait Number<X, T> {
        #[allow(unused)]
        fn fake(x: X) -> T;
    }

    #[trait_gen(T -> f32, f64)]
    // all trait arguments must change:
    impl Number<T, T> for T {
        #[allow(unused)]
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
    use std::ops::Neg;
    use trait_gen::trait_gen;

    #[derive(PartialEq, Debug)]
    struct Meter<U>(U);
    #[derive(PartialEq, Debug)]
    struct Foot<U>(U);

    trait GetLength<T> {
        fn length(&self) -> T;
    }

    // Type method implementations

    #[trait_gen(T -> f32, f64)]
    #[trait_gen(U -> Meter<T>, Foot<T>)]
    impl U {
        fn scale(&self, value: T) -> U {
            U(self.0 * value)
        }
    }

    // Without the macro:
    //
    // use std::ops::Mul;
    //
    // impl<T: Mul<T, Output = T> + Copy> Meter<T> {
    //     fn scale(&self, value: T) -> Meter<T> {
    //         Meter(self.0 * value)
    //     }
    // }
    //
    // impl<T: Mul<T, Output = T> + Copy> Foot<T> {
    //     fn scale(&self, value: T) -> Foot<T> {
    //         Foot(self.0 * value)
    //     }
    // }

    // Trait implementations

    #[trait_gen(T -> Meter<U>, Foot<U>)]
    #[trait_gen(U -> f32, f64)]
    impl GetLength<U> for T {
        fn length(&self) -> U {
            self.0 as U
        }
    }

    #[trait_gen(T -> Meter<U>, Foot<U>)]
    #[trait_gen(U -> f32, f64)]
    impl Neg for T {
        type Output = T;

        fn neg(self) -> Self::Output {
            T(-self.0)
        }
    }

    #[test]
    fn test() {
        let m_32 = Meter(1.0_f32);
        let m_64 = Meter(2.0_f64);
        let f_32 = Foot(3.0_f32);
        let f_64 = Foot(4.0_f64);
        assert_eq!(m_32.length(), 1.0_f32);
        assert_eq!(m_64.length(), 2.0_f64);
        assert_eq!(f_32.length(), 3.0_f32);
        assert_eq!(f_64.length(), 4.0_f64);
        assert_eq!(m_32.scale(10.0), Meter(10.0_f32));
        assert_eq!(m_64.scale(10.0), Meter(20.0_f64));
        assert_eq!(f_32.scale(10.0), Foot(30.0_f32));
        assert_eq!(f_64.scale(10.0), Foot(40.0_f64));
        assert_eq!(-m_32, Meter(-1.0_f32));
        assert_eq!(-m_64, Meter(-2.0_f64));
        assert_eq!(-f_32, Foot(-3.0_f32));
        assert_eq!(-f_64, Foot(-4.0_f64));
    }
}

mod impl_cond {
    use trait_gen::{trait_gen, trait_gen_if};

    trait Binary {
        const MSB: u32;
        const IS_REF: bool;
        fn msb(self) -> u32;
        fn is_ref(self) -> bool;
    }

    // with this ordering, the #[trait_gen_if] see either
    // - T = u8, u16, or u32
    // - U = u8, u16, u32, &u8, &u16, or &u32
    #[trait_gen(T -> u8, u16, u32)]
    #[trait_gen(U -> T, &T)]
    impl Binary for U {
        #[trait_gen_if(U in [u8, &u8])] // #[trait_gen_if(T in u8])] works, too
        const MSB: u32 = 7;
        #[trait_gen_if(U in u16, &u16)]
        const MSB: u32 = 15;
        #[trait_gen_if(U in u32, &u32)]
        const MSB: u32 = 31;
        #[trait_gen_if(U in u64, &u64)]
        const MSB: u32 = 63;
        #[trait_gen_if(U in u128, &u128)]
        const MSB: u32 = 127;
        #[trait_gen_if(U in u8, u16, u32)]
        const IS_REF: bool = false;
        #[trait_gen_if(U in &u8, &u16, &u32)]
        const IS_REF: bool = true;

        fn msb(self) -> u32 {
            Self::MSB
        }

        /// Is ${U} a reference?
        fn is_ref(self) -> bool {
            Self::IS_REF
        }
    }

    #[test]
    fn test_msb() {
        let tests = vec![
            (1_u8.msb(),        7,      1_u8.is_ref(),      false),
            ((&1_u8).msb(),     7,      (&1_u8).is_ref(),   true),
            (1_u16.msb(),       15,     1_u16.is_ref(),     false),
            ((&1_u16).msb(),    15,      (&1_u8).is_ref(),  true),
            (1_u32.msb(),       31,     1_u32.is_ref(),     false),
            ((&1_u32).msb(),    31,     (&1_u32).is_ref(),  true),
        ];
        for (index, (result_msb, expected_msb, result_is_ref, expected_is_ref)) in tests.into_iter().enumerate() {
            assert_eq!(result_msb, expected_msb, "test {index} failed on msb");
            assert_eq!(result_is_ref, expected_is_ref, "test {index} failed on is_ref");
        }
    }
}

mod impl_cond2 {
    use trait_gen::{trait_gen, trait_gen_if};

    trait Binary {
        const MSB: u32;
        const IS_REF: bool;
        fn msb(self) -> u32;
        fn is_ref(self) -> bool;
    }

    // with this ordering, the #[trait_gen_if] see either
    // - U = T or &T
    // - T = u8, u16, or u32
    #[trait_gen(U -> T, &T)]
    #[trait_gen(T -> u8, u16, u32)]
    impl Binary for U {
        #[trait_gen_if(T in u8)]
        const MSB: u32 = 7;
        #[trait_gen_if(T in u16)]
        const MSB: u32 = 15;
        #[trait_gen_if(T in u32)]
        const MSB: u32 = 31;
        #[trait_gen_if(T in u64)]
        const MSB: u32 = 63;
        #[trait_gen_if(T in u128)]
        const MSB: u32 = 127;

        #[trait_gen_if(U in T)]
        const IS_REF: bool = false;
        #[trait_gen_if(U in &T)]
        const IS_REF: bool = true;

        fn msb(self) -> u32 {
            Self::MSB
        }

        /// Is ${U} a reference?
        fn is_ref(self) -> bool {
            Self::IS_REF
        }
    }

    #[test]
    fn test_msb() {
        let tests = vec![
            (1_u8.msb(),        7,      1_u8.is_ref(),      false),
            ((&1_u8).msb(),     7,      (&1_u8).is_ref(),   true),
            (1_u16.msb(),       15,     1_u16.is_ref(),     false),
            ((&1_u16).msb(),    15,      (&1_u8).is_ref(),  true),
            (1_u32.msb(),       31,     1_u32.is_ref(),     false),
            ((&1_u32).msb(),    31,     (&1_u32).is_ref(),  true),
        ];
        for (index, (result_msb, expected_msb, result_is_ref, expected_is_ref)) in tests.into_iter().enumerate() {
            assert_eq!(result_msb, expected_msb, "test {index} failed on msb");
            assert_eq!(result_is_ref, expected_is_ref, "test {index} failed on is_ref");
        }
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

mod ex04 {
    use trait_gen::trait_gen;

    trait A where Self: Sized {
        fn a(self) -> i32 { 1 }
    }

    trait B where Self: Sized {
        fn b(self) -> i32 { 2 }
    }

    // Use the macro to generate multiple traits for different types
    #[trait_gen(T -> u32, i32, u64, i64)]
    #[trait_gen(U -> A, B)]
    impl U for T {}

    #[test]
    fn test() {
        let u = 10_u32;
        let v = 10_i32;
        let w = 10_u64;
        let x = 10_i64;

        assert_eq!(u.a(), 1);
        assert_eq!(v.a(), 1);
        assert_eq!(w.a(), 1);
        assert_eq!(x.a(), 1);

        assert_eq!(u.b(), 2);
        assert_eq!(v.b(), 2);
        assert_eq!(w.b(), 2);
        assert_eq!(x.b(), 2);
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

    // type T = u64;
    
    #[trait_gen(T -> u64, i64, u32, i32, u16, i16, u8, i8)]
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

// =============================================================================
// Non-trait implementations.
// -----------------------------------------------------------------------------

mod impl_type_01 {
    use trait_gen::trait_gen;
    use super::{Foot, Meter};

    #[trait_gen(T -> f32, f64)]
    impl Foot<T> {
        const METERS_TO_FEET: T = 3.372;
        fn from_meter(x: Meter<T>) -> Self {
            Foot(x.0 * Self::METERS_TO_FEET)
        }
    }

    #[test]
    fn test() {
        assert_eq!(Foot::<f32>::from_meter(Meter(1.0_f32)).0, 3.372_f32);
        assert_eq!(Foot::<f64>::from_meter(Meter(1.0_f64)).0, 3.372_f64);
        assert_eq!(Foot::<f32>::METERS_TO_FEET, 3.372_f32);
        assert_eq!(Foot::<f64>::METERS_TO_FEET, 3.372_f64);
    }
}

mod impl_type_02 {
    use trait_gen::trait_gen;
    use super::{Foot, Meter};

    #[trait_gen(T -> f32, f64)]
    impl Meter<T> {
        fn from_foot<F>(x: Foot<F>) -> Self where T: From<F> {
            Meter(T::from(x.0) / 3.372)
        }
    }

    #[test]
    fn test() {
        assert!((Meter::<f32>::from_foot(Foot(1.0_f32)).0 - 0.29656_f32).abs() < 1e-5);
        assert!((Meter::<f64>::from_foot(Foot(1.0_f32)).0 - 0.29656_f64).abs() < 1e-5);
        assert!((Meter::<f64>::from_foot(Foot(1.0_f64)).0 - 0.29656_f64).abs() < 1e-5);
    }
}

#[cfg(feature = "type_gen")]
mod type_gen {
    use trait_gen::{type_gen, type_gen_if};

    struct Meter<T>(T);
    struct Foot<T>(T);

    #[type_gen(T -> f32, f64)]
    impl Foot<T> {
        #[type_gen_if(T in f32)]
        const METERS_TO_FEET: T = 3.37;    // rounded for the sake of the test
        #[type_gen_if(T in f64)]
        const METERS_TO_FEET: T = 3.372;
        fn from_meter(x: Meter<T>) -> Self {
            Foot(x.0 * Self::METERS_TO_FEET)
        }
    }

    #[test]
    fn test() {
        assert_eq!(Foot::<f32>::from_meter(Meter(1.0_f32)).0, 3.37_f32);
        assert_eq!(Foot::<f64>::from_meter(Meter(1.0_f64)).0, 3.372_f64);
        assert_eq!(Foot::<f32>::METERS_TO_FEET, 3.37_f32);
        assert_eq!(Foot::<f64>::METERS_TO_FEET, 3.372_f64);
    }
}

mod trait_gen_if_alone {
    use trait_gen::trait_gen_if;

    // Note: this attribute really shouldn't be used alone. If you want to disable code, use `#[cfg(any())]`.

    #[trait_gen_if(() in ())]
    struct Necessary;

    #[trait_gen_if(!() in ())]
    #[test]
    fn failure() {
        panic!("This shouldn't exist")
    }

    #[test]
    fn test() {
        let _a: Necessary;
    }
}
