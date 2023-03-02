# Change notes

<!-- TOC -->
* [Change notes](#change-notes)
  * [1. Type constructors](#1-type-constructors)
    * [The `syn` library](#the-syn-library)
    * [Analysis](#analysis)
    * [Choice of implementation](#choice-of-implementation)
  * [2. Generics and cross-product generators](#2-generics-and-cross-product-generators)
    * [Generic forms](#generic-forms)
    * [Structure of generics in AST](#structure-of-generics-in-ast)
<!-- TOC -->


## 1. Type constructors

Improves the awareness of the position within the AST, to tell the difference between 
constants and types in ambiguous situations.

This allows to use types in expressions when it was not possible before.

```rust
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
```

### The `syn` library

`visit_path_mut` is used in:

```text
visit_attribute_mut         `#[mystuff(T -> u64, i64)]`
                               ^^^^^^^
visit_expr_path_mut         `let x = Some(value)` or `const T: f64 = 0.0; let x = T + 2.0;`
                                     ^^^^                                         ^
visit_expr_struct_mut       `let x = T { size: 0.0 }`
                                     ^
visit_item_impl_mut         `impl<A> Trait for Data<A> { ... }`
                                     ^^^^^
visit_macro_mut             `println!("...")`
                             ^^^^^^^
visit_meta_list_mut         `#[derive(Copy, Clone)]`
                               ^^^^^^
visit_meta_mut              `#[inline]`
                               ^^^^^^
visit_meta_name_value_mut   `#[path = "sys/windows.rs"]`
                               ^^^^
visit_pat_path_mut          `match c { Color::Red => `
                                       ^^^^^^^^^^
visit_pat_struct_mut        `match c { Data::Style { .. } => `
                                       ^^^^^^^^^^^
visit_pat_tuple_struct_mut  `match c { Some(answer) => `
                                       ^^^^
visit_trait_bound_mut       `impl <T: Copy> Trait for MyType<T> where T: Display`
                                      ^^^^                               ^^^^^^^
visit_type_path_mut         `let x: outside::T<U> = x as outside::T<U>`
                                    ^^^^^^^^^^^^^        ^^^^^^^^^^^^^
visit_vis_restricted_mut    `pub(crate)` or `pub(in some::module)`
                                 ^^^^^              ^^^^^^^^^^^^
```

The only problem, except generics, comes from `expr_path`, which is used for any identifier
in an expression. Normally, the only possible collision is with a constant of the same name
(including the path to it).

It is acceptable to dismiss the generics problem by generating an error in case of
collision. At worst, it avoids confusing code.

### Analysis

The different cases where `Path` is used, in `Expr`:

    pub enum Expr {
            // ...
            Cast(ExprCast),
            Path(ExprPath),
            Struct(ExprStruct),
            // ...
            Type(ExprType),     // note: type ascription is still experimental
            // ...
    }

* `ExprCast` must be translated, it's not an issue:
 
      pub struct ExprCast {
          pub attrs: Vec<Attribute>,
          pub expr: Box<Expr>,
          pub as_token: Token![as],
          pub ty: Box<Type>,
      }

* `ExprStruct` must be translated, it's not an issue:

      pub struct ExprStruct #full {
          pub attrs: Vec<Attribute>,
          pub path: Path,
          pub brace_token: token::Brace,
          pub fields: Punctuated<FieldValue, Token![,]>,
          pub dot2_token: Option<Token![..]>,
          pub rest: Option<Box<Expr>>,
      }

* `ExprType` must be translated too:

      pub struct ExprType #full {
          pub attrs: Vec<Attribute>,
          pub expr: Box<Expr>,
          pub colon_token: Token![:],
          pub ty: Box<Type>,          // -> Path(TypePath) for instance
      }

* `ExprPath` is not straightforward:

      pub struct ExprPath {
          pub attrs: Vec<Attribute>,
          pub qself: Option<QSelf>,
          pub path: Path,
      }

  * `let x = T(value)`:
    * `ExprCall -> func:ExprPath -> Path("T")`   
    
    Possible conflicts if an enumeration has an item with a
     conflicting name, which should be avoidable by adding the type path in front
    (it should be there in the first place)

    => best to replace, it could be a constructor of the attribute type parameter 
    if it's an `enum`.

  * `const T: f64 = 0.0; let x = T + 2.0;`:
    * `Expr -> Path(ExprPath) -> Path("T")`

    => cannot replace.

**In summary**:
* when `ExprPath`
  * when parent is `ExprCall`, replace
  * other cases, don't replace
* other cases, replace

The call hierarchy is shown for typical cases below.

Must be ENABLED in visit_path_mut: 

    visit_expr_mut(self, node0 = Expr::Call(node1: ExprCall))
      - enable -
      visit_expr_call_mut(self, node1 = ExprCall { func: Expr::Path(ExprPath) )
        visit_expr_mut(self, node2 = Expr::Path(ExprPath))
          - no change -
          visit_expr_path_mut(self, node3 = ExprPath { path: Path, .. })
            visit_path_mut(self, path)                                    

Must be ENABLED in visit_path_mut: 

    visit_expr_mut(self, node0 = Expr::Cast(node1: ExprCast))
      - (enable) -
      visit_expr_cast_mut(self, node1 = ExprCast { expr: Expr, ty: Type, ..)
        visit_expr_mut(self, node2 = expr)
          - (either enable or disable, depending on the expression) -
        visit_type_mut(self, node3 = ty)   with for example ty = Type::Path(TypePath)
          visit_type_path_mut(self, node4 = TypePath { path, ... })
            - enable -
            visit_path_mut(self, node5 = path)

Must be DISABLED in visit_path_mut: 

    visit_expr_mut(self, node0 = Expr::Binary(node1: ExprBinary))
      - disable -
      visit_expr_binary_mut(self, node1 = ExprBinary { left: Expr, right: Expr, ..)  with for ex. left = ExprPath
        visit_expr_mut(self, left = Expr::Path(ExprPath))
          - no change -
          visit_expr_path_mut(self, node3 = ExprPath { path: Path, .. })
            visit_path_mut(self, path)
        ...

### Choice of implementation

Solution adopted: 
* Adding a substitution authorization stack in the `Types` object. 
* Peeking at the top of the stack tells whether we can substitute or not. 
* Authorizations are pushed in nodes like `ExprCall` before calling the internal visitors, 
  then popped after (the return from) the call. 

This is much safer than changing the state of the `Types` object, for instance, in the
different visitors. And it's much shorter than re-implementing the logic of the visitors,
especially since the helpers and other functions or data are private to `syn`.


 
