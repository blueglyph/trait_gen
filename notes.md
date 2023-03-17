# Change notes

<!-- TOC -->
* [Change notes](#change-notes)
  * [1. Type constructors](#1-type-constructors)
    * [The `syn` library](#the-syn-library)
    * [Analysis](#analysis)
    * [Choice of implementation](#choice-of-implementation)
  * [2. From Path to Type](#2-from-path-to-type)
    * [The `syn` library](#the-syn-library-1)
    * [Cases](#cases)
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
            Call(ExprCall),
            Cast(ExprCast),
            Path(ExprPath),
            Struct(ExprStruct),
            // ...
            Type(ExprType),
            // ...
    }

* `ExprCall` must be translated:

      pub struct ExprCall {
          pub attrs: Vec<Attribute>,
          pub func: Box<Expr>,      // -> Path(ExprPath) for instance in `T::new(0)`
          pub paren_token: token::Paren,
          pub args: Punctuated<Expr, Token![,]>,
      }

* `ExprCast` must be translated:
 
      pub struct ExprCast {
          pub attrs: Vec<Attribute>,
          pub expr: Box<Expr>,
          pub as_token: Token![as],
          pub ty: Box<Type>,        // -> Path(TypePath) in `as T`
      }

* `ExprStruct` must be translated:

      pub struct ExprStruct #full {
          pub attrs: Vec<Attribute>,
          pub path: Path,           // -> in `T { field: value }`          
          pub brace_token: token::Brace,
          pub fields: Punctuated<FieldValue, Token![,]>,
          pub dot2_token: Option<Token![..]>,
          pub rest: Option<Box<Expr>>,
      }

* `ExprType` must be translated too (type ascription is still experimental):

      pub struct ExprType #full {
          pub attrs: Vec<Attribute>,
          pub expr: Box<Expr>,
          pub colon_token: Token![:],
          pub ty: Box<Type>,        // -> Path(TypePath) in `data.collect() : T`
      }                             

* `ExprPath` is not straightforward:

      pub struct ExprPath {
          pub attrs: Vec<Attribute>,
          pub qself: Option<QSelf>,
          pub path: Path,           // -> in `T::CONSTANT` 
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

## 2. From Path to Type

Instead of simple paths in the attribute parameters, we would like references and possibly other type syntaxes.

```rust
#[trait_gen(T -> &U, &mut U, Box<U>)]
#[trait_gen(U -> u8, u16, u32, u64, u128)]
impl IntLog for T {
    fn log10(self) -> usize {
        IntLog::log10(*self)
    }
    fn log2(self) -> usize {
        IntLog::log10(*self)
    }
}
```

where 
* `&U` and `&mut U` are `Type::Reference(TypeReference)`
* `Box<U>` is `Type::Path(TypePath)`

### The `syn` library

Currently, the substitution is done when visiting a `syn::Path` and checking if the prefixes of its segments match the attribute generic parameter (`T` in `#[trait_gen(T -> repl1, repl2)]`).

Allowing more general substitutions requires to parse `syn::ty::Type` parameters. Here are a few relevant variants of this type:

```rust
pub enum Type {
    /// A fixed size array type: `[T; n]`.
    Array(TypeArray),

    /// A bare function type: `fn(usize) -> bool`.
    BareFn(TypeBareFn),

    /// A type contained within invisible delimiters. (?)
    Group(TypeGroup),
    
    /// A parenthesized type equivalent to the inner type (?).
    Paren(TypeParen),
    
    /// A path like `super::U`, optionally qualified like `<T as Trait>::C`.
    Path(TypePath),

    /// A raw pointer type: `*const T` or `*mut T`.
    Ptr(TypePtr),

    /// A reference type: `&'a T` or `&'a mut T`.
    Reference(TypeReference),

    /// A dynamically sized slice type: `[T]`.
    Slice(TypeSlice),

    /// A tuple type: `(A, B, C, String)`.
    Tuple(TypeTuple),

    // ...
}
```

### Cases

Here is a simple example:

```rust
impl AddMod for &U
impl AddMod for &mut U
```

are `ItemImpl`, in which `self_ty` is `Type::Reference(TypeReference)`

```rust
impl AddMod for Box<U>
```

is an `ItemImpl`, in which `self_ty` is `Type::Path(TypePath)`

```rust
    pub struct ItemImpl {
        pub attrs: Vec<Attribute>,
        pub defaultness: Option<Token![default]>,
        pub unsafety: Option<Token![unsafe]>,
        pub impl_token: Token![impl],
        pub generics: Generics,
        pub trait_: Option<(Option<Token![!]>, Path, Token![for])>,
        pub self_ty: Box<Type>,     // <== to replace
        pub brace_token: token::Brace,
        pub items: Vec<ImplItem>,
    }
```

What are all the cases? There are many of them:

*   ```rust
    /// A field of a struct or enum variant.
    pub struct Field {
    /// A cast expression: `foo as f64`.
    pub struct ExprCast {
    /// A type ascription expression: `foo: f64`.
    pub struct ExprType #full {
    /// An individual generic argument to a method, like `T`.
    pub enum GenericMethodArgument {
    /// A generic type parameter: `T: Into<String>`.
    pub struct TypeParam {
    /// A const generic parameter: `const LENGTH: usize`.
    pub struct ConstParam {
    /// A type predicate in a `where` clause: `for<'c> Foo<'c>: Trait<'c>`.
    pub struct PredicateType {
    /// An equality predicate in a `where` clause (unsupported).
    pub struct PredicateEq {
    /// A constant item: `const MAX: u16 = 65535`.
    pub struct ItemConst {
    /// An impl block providing trait or associated items: `impl<A> Trait
    pub struct ItemImpl {
    /// A static item: `static BIKE: Shed = Shed(42)`.
    pub struct ItemStatic {
    /// A type alias: `type Result<T> = std::result::Result<T, MyError>`.
    pub struct ItemType {
    /// A foreign static item in an `extern` block: `static ext: u8`.
    pub struct ForeignItemStatic {
    /// An associated constant within the definition of a trait.
    pub struct TraitItemConst {
    /// An associated type within the definition of a trait.
    pub struct TraitItemType {
    /// An associated constant within an impl block.
    pub struct ImplItemConst {
    /// An associated type within an impl block.
    pub struct ImplItemType {
    /// A type ascription pattern: `foo: f64`.
    pub struct PatType {
    /// An individual generic argument, like `'a`, `T`, or `Item = T`.
    pub enum GenericArgument {
    /// A binding (equality constraint) on an associated type: `Item = u8`.
    pub struct Binding {
    /// Arguments of a function path segment: the `(A, B) -> C` in `Fn(A,B) -> C`.
    pub struct ParenthesizedGenericArguments {
    /// The explicit Self type in a qualified path: the `T` in `<T as Display>::fmt`.
    pub struct QSelf {
    /// A fixed size array type: `[T; n]`.
    pub struct TypeArray {
    /// A type contained within invisible delimiters.
    pub struct TypeGroup {
    /// A parenthesized type equivalent to the inner type.
    pub struct TypeParen {
    /// A raw pointer type: `*const T` or `*mut T`.
    pub struct TypePtr {
    /// A reference type: `&'a T` or `&'a mut T`.
    pub struct TypeReference {
    /// A dynamically sized slice type: `[T]`.
    pub struct TypeSlice {
    /// A tuple type: `(A, B, C, String)`.
    pub struct TypeTuple {
    /// An argument in a function type: the `usize` in `fn(usize) -> bool`.
    pub struct BareFnArg {
    /// Return type of a function signature.
    pub enum ReturnType {
    ```

