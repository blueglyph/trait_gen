#![allow(unused_imports)]
#![allow(unused_variables)]

use std::ops::{Add, Neg};
use typegen::typegen;

#[derive(Clone, Copy)]
/// Distance in meter
pub struct Meter(f64);

#[derive(Clone, Copy)]
/// Distance in meter
pub struct Foot(f64);

#[derive(Clone, Copy)]
/// Distance in miles
pub struct Mile(f64);

type T = Foot;
#[typegen(T, Meter, Mile)]
impl Add for T {
    type Output = T;

    fn add(self, rhs: Self) -> Self::Output {
        // The first type identifier, here 'T', must not be redefined by a generic because the macro
        // cannot handle the scopes.
        //
        // Uncomment to test that this is detected and generates an error:
        // --------------------------------
        // fn fake<T: Sized>(_x: T) {
        //     println!("x-x");
        // }
        // fake(1_u32);
        // --------------------------------

        // Note that it is not possible to use a type alias to instantiate an object, so here
        // we use `Self( ... )` and not `T( ... )`. The intermediate `result` variable is optional
        // and it is only used here to test the type substitution:

        let result: T = Self(self.0 + rhs.0);
        result
    }
}

#[test]
fn test_substitution() {
    let a = Meter(1.0);
    let b = Meter(2.0);

    let c = a + b;
    assert_eq!(c.0, 3.0);
}

// Not yet implemented, the initial type is simply substituted by the first type of the list:
//
// #[test]
// fn test_multiple_types() {
//     let fa = Foot(1.0);
//     let fb = Foot(2.0);
//
//     let fc = fa + fb;
//     assert_eq!(fc.0, 3.0);
//
//     let ma = Mile(1.0);
//     let mb = Mile(2.0);
//
//     let mc = ma + mb;
//     assert_eq!(mc.0, 3.0);
// }
