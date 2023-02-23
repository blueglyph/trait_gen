use proc_macro_error::proc_macro_error;
use proc_macro::TokenStream;
use proc_macro2::Ident;
use proc_macro_error::abort;

use syn::{ItemImpl, PathSegment, Generics, parse_quote, GenericParam, Token, parse_macro_input};
use quote::quote;
use syn::fold::Fold;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;

#[derive(Debug)]
struct Types {
    current_type: Ident,
    new_types: Vec<Ident>
}

impl Fold for Types {

    /// Triggers an error when a generic with the same name type is used:
    fn fold_generics(&mut self, i: Generics) -> Generics {
        for t in i.params.iter() {
            match &t {
                GenericParam::Type(t) => {
                    println!("Generics - Type {}", t.ident);
                    if t.ident == self.current_type {
                        let col_start: proc_macro::Span = t.span().unwrap();
                        println!("col_start: {:?}", col_start);
                        abort!(t.span(),
                            "Type '{}' is reserved for the substitution.", self.current_type.to_string();
                            help = "Use another identifier for this local generic type."
                        );

                        // Other attempts at generating an error message:

                        // Yet another unstable feature:
                        // ----------------------------
                        // t.span().unwrap()
                        //     .error(ERROR_MSG)
                        //     .emit();

                        // This doesn't work well because it has to be inserted at the right to
                        // avoid generating a syntax error:
                        // --------------------------------------------------------------------
                        // return parse_quote_spanned!{
                        //     i.span() => compile_error!(ERROR_MSG)
                        // }
                        //
                        // or
                        //
                        // return parse_quote_spanned!(t.span() =>
                        //     compile_error!(#ERROR_MSG)
                        // );

                        // `panic!` works but doesn't give the location and shows a generic
                        // error message (the useful part is lower in the "help" part):
                        // ----------------------------------------------------------------
                        // panic!("{ERROR_MSG}");
                        //
                        // error: custom attribute panicked
                        //   --> tests\integration.rs:25:1
                        //    |
                        // 25 | #[return_as_is]
                        //    | ^^^^^^^^^^^^^^^
                        //    |
                        //    = help: message: Type 'T' is reserved for the substitution. Use ...

                    }
                }
                _ => {}
            }
        }
        i
    }

    fn fold_path_segment(&mut self, ps: PathSegment) -> PathSegment {
        let ident: &Ident = &ps.ident;
        // let args: &PathArguments = &ps.arguments;
        // print!("PathSemgnt.ident: {ident}, args: ");
        // match args {
        //     PathArguments::None => println!("none"),
        //     PathArguments::AngleBracketed(_) => println!("<'a, T>"),
        //     PathArguments::Parenthesized(_) => println!("(A, B) -> C"),
        // };
        if ident == &self.current_type {
            let new_type = self.new_types.first().unwrap();
            parse_quote!(#new_type)
        } else {
            ps
        }
    }
}

impl Parse for Types {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let vars = Punctuated::<Ident, Token![,]>::parse_terminated(input)?;
        let mut new_types: Vec<Ident> = vars.into_iter().collect();
        let current_type = new_types.remove(0);
        Ok(Types { current_type, new_types })
    }
}


#[proc_macro_attribute]
#[proc_macro_error]
pub fn typegen(args: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemImpl);
    let mut types = parse_macro_input!(args as Types);

    // Only first changed:
    // ------------------------------------------------------------------
    // let modified = types.fold_item_impl(input);
    // TokenStream::from(quote!(#modified))

    // No change:
    // ------------------------------------------------------------------
    // TokenStream::from(quote!(#input))

    // All changed:
    // ------------------------------------------------------------------
    // let mut output = TokenStream::from(quote!(input.clone()));
    let mut output = TokenStream::new();
    while !types.new_types.is_empty() {
        println!("implementing {}", types.new_types.first().unwrap());
        let modified = types.fold_item_impl(input.clone());
        output.extend(TokenStream::from(quote!(#modified)));
        types.new_types.remove(0);
    }

    println!("implementing {}", types.current_type);
    output.extend(TokenStream::from(quote!(#input)));
    output

    // Tests that more implementations can be added to output:
    // ------------------------------------------------------
    // println!("item = {:#?}", item);
    // let input = parse_macro_input!(item as ItemImpl);
    // let output = TokenStream::from(quote!(
    //     #input
    //
    //     impl Add for Foot {
    //         type Output = Foot;
    //
    //         fn add(self, rhs: Self) -> Self::Output {
    //             Foot(self.0 + rhs.0)
    //         }
    //     }
    //
    // ));
    // println!("output = {:#?}", output);
    // output
    //
    // => works fine
}
