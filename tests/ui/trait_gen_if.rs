#![allow(unused)]
use trait_gen::{trait_gen, trait_gen_if};

trait Binary {
    const MSB: u32;
}

// missing generic argument
#[trait_gen(T -> u8, u16, u32)]
impl Binary for U {
    #[trait_gen_if( in u8)]
    const MSB: u32 = 7;
}

// '->' instead of 'in'
#[trait_gen(T -> u8, u16, u32)]
impl Binary for U {
    #[trait_gen_if(U -> u8)]
    const MSB: u32 = 7;
}

// missing types
#[trait_gen(T -> u8, u16, u32)]
impl Binary for U {
    #[trait_gen_if(T in)]
    const MSB: u32 = 7;
}

// missing punctuation
#[trait_gen(T -> u8, &u8, u16, &u16)]
impl Binary for U {
    #[trait_gen_if(T in u8 &u8)]
    const MSB: u32 = 7;
}

// missing arguments
#[trait_gen(T -> u8, &u8, u16, &u16)]
impl Binary for U {
    #[trait_gen_if]
    const MSB: u32 = 7;
}

// missing arguments
#[trait_gen(T -> u8, &u8, u16, &u16)]
impl Binary for U {
    #[trait_gen_if()]
    const MSB: u32 = 7;
}

fn main() {}