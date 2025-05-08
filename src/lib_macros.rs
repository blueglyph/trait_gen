// Copyright 2023 Redglyph
//
// Top-level macro code. Independent of proc_macro.

use proc_macro2::TokenStream;
use proc_macro_error::abort;
use quote::quote;
use syn::File;
use syn::visit_mut::VisitMut;
use crate::args::{ArgType, CondParams, TraitGen};
use crate::subst::{to_subst_types, Subst};
use crate::utils::pathname;

// For verbose debugging
pub(crate) const VERBOSE: bool = false;
pub(crate) const VERBOSE_TF: bool = false;

//==============================================================================
// Main code of the substitution attribute

fn substitute(item: TokenStream, mut types: Subst) -> TokenStream {
    if VERBOSE || VERBOSE_TF {
        println!("{}\ntrait_gen for {} -> {}: {}",
                 "=".repeat(80),
                 pathname(&types.generic_arg),
                 if types.is_path { "PATH" } else { "TYPE" },
                 &types.types.iter().map(pathname).collect::<Vec<_>>().join(", ")
        )
    }
    if VERBOSE || VERBOSE_TF { println!("\n{}\n{}", item, "-".repeat(80)); }
    let mut output = TokenStream::new();
    let ast: File = syn::parse2(item).unwrap();
    while !types.types.is_empty() {
        let mut modified_ast = ast.clone();
        types.visit_file_mut(&mut modified_ast);
        output.extend(TokenStream::from(quote!(#modified_ast)));
        assert!(types.can_subst_path.is_empty(), "self.enabled has {} entries after type {}",
                types.can_subst_path.len(), pathname(types.types.first().unwrap()));
        types.types.remove(0);
    }
    if VERBOSE { println!("end trait_gen for {}\n{}", pathname(&types.generic_arg), "-".repeat(80)); }
    output
}

pub(crate) fn macro_trait_gen(args: TokenStream, item: TokenStream) -> TokenStream {
    let mut attribute = match syn::parse2::<TraitGen>(args) {
        Ok(types) => types,
        Err(err) => abort!(err.span(), err;
            help = "The expected format is: #[trait_gen(T -> Type1, Type2, Type3)]"),
    };
    let mut output = TokenStream::new();
    let args = std::mem::replace(&mut attribute.args, ArgType::None);
    match &args {
        ArgType::Tuple(paths) => {
            // generates all the permutations
            let mut subst = Subst::from_trait_gen(attribute.clone(), paths[0].clone());
            let types = std::mem::take(&mut subst.types);
            let new_iterators = (0..paths.len()).map(|_| types.iter()).collect::<Vec<_>>();
            let mut values = vec![];
            let mut iterators = vec![];
            loop {
                // fill missing iterators with fresh ones:
                for mut new_iter in new_iterators.iter().skip(iterators.len()).cloned() {
                    values.push(new_iter.next().unwrap());
                    iterators.push(new_iter);
                }
                // do the substitutions:
                let mut stream = item.clone();
                for (arg, &ty) in paths.iter().zip(values.iter()) {
                    subst.generic_arg = arg.clone();
                    subst.types = vec![ty.clone()];
                    stream = substitute(stream, subst.clone());
                }
                output.extend(stream);
                // pops dead iterators and increases the next one:
                while let Some(mut it) = iterators.pop() {
                    values.pop();
                    if let Some(v) = it.next() {
                        values.push(v);
                        iterators.push(it);
                        break;
                    }
                }
                if values.is_empty() { break }
            }
        }
        ArgType::Permutation(path1, path2) | ArgType::StrictOrder(path1, path2) | ArgType::NonStrictOrder(path1, path2) => {
            // we could translate the attribute into simple attributes using conditionals, but it's
            // easier, lighter, and safer to simply generate and filter the combinations
            let (_, types) = to_subst_types(attribute.types.clone());
            let mut subst = Subst::from_trait_gen(attribute.clone(), path1.clone());
            for (i1, p1) in types.iter().enumerate() {
                for (i2, p2) in types.iter().enumerate() {
                    let cond = match &args {
                        ArgType::Permutation(_, _) => i1 != i2,
                        ArgType::StrictOrder(_, _) => i1 < i2,
                        ArgType::NonStrictOrder(_, _) => i1 <= i2,
                        _ => panic!("can't happen")
                    };
                    if cond {
                        subst.types = vec![p1.clone()];
                        subst.generic_arg = path1.clone();
                        let stream = substitute(item.clone(), subst.clone());
                        subst.types = vec![p2.clone()];
                        subst.generic_arg = path2.clone();
                        output.extend(substitute(stream, subst.clone()));
                    }
                }
            }
        }
        _ => panic!("can't happen"),
    }
    if VERBOSE { println!("{}\n{}", output, "=".repeat(80)); }
    output
}

//==============================================================================
// Main code of the conditional attribute

pub(crate) fn macro_trait_gen_if(name: &str, args: TokenStream, item: TokenStream) -> TokenStream {
    if VERBOSE { println!("process_conditional_attribute({}, {})", args.to_string(), item.to_string()); }
    let new_code = match syn::parse2::<CondParams>(args) {
        Ok(attr) => {
            if attr.types.contains(&attr.generic_arg) ^ attr.is_negated {
                item                // enables the code
            } else {
                TokenStream::new()  // disables the code
            }
        }
        Err(err) => {
            // shouldn't happen, unless the attribute is used out of a #[trait_gen] attribute scope
            abort!(err.span(), err;
            help = "The expected format is: #[{}(T in Type1, Type2, Type3)]", name);
        }
    };
    new_code
}

