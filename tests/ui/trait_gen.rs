use trait_gen::trait_gen;

struct Test<T>(T);

// missing generic argument
#[trait_gen(-> i16, u16)]
impl Test<T> {
    fn test() -> bool { true }
}

// old 'in' format instead of '->'
#[trait_gen(T in i16, u16)]
impl Test<T> {
    fn test() -> bool { true }
}

// missing types
#[trait_gen(T -> )]
impl Test<T> {
    fn test() -> bool { true }
}

// missing punctuation
#[trait_gen(T -> i16 u16)]
impl Test<T> {
    fn test() -> bool { true }
}

// missing arguments
#[trait_gen]
impl Test<T> {
    fn test() -> bool { true }
}

// missing arguments
#[trait_gen()]
impl Test<T> {
    fn test() -> bool { true }
}

// bad punctuation: ';' instead of ','
#[trait_gen(T; U -> u16, u32)]
impl Test<T> {
    fn test() -> bool { true }
}

// bad punctuation: '!!' instead of '!='
#[trait_gen(T !! U -> u16, u32)]
impl Test<T> {
    fn test() -> bool { true }
}

// conflict between generic arguments
#[trait_gen(T -> u64, i64, u32, i32)]
impl AddMod for T {
    type Output = T;

    fn add_mod(self, rhs: Self, modulo: Self) -> Self::Output {
        fn int_mod<T: Num> (a: T, m: T) -> T { // <== ERROR, conflicting 'T'
            a % m
        }
        int_mod(self + rhs, modulo)
    }
}

fn main() {}