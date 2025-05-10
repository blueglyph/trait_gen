// Copyright (c) 2025 Redglyph (@gmail.com). All Rights Reserved.
//
// Helper functions and traits. Independent of proc_macro.

use quote::ToTokens;
use syn::{GenericArgument, Path, PathArguments, PathSegment};

//==============================================================================
// Helper traits

trait NodeMatch {
    /// Checks if the `self` node is a prefix of `other`.
    fn match_prefix(&self, other: &Self) -> bool;
}

impl NodeMatch for GenericArgument {
    /// Compares both generic arguments, disregarding lifetime argument names
    fn match_prefix(&self, other: &Self) -> bool {
        if let GenericArgument::Lifetime(_) = self {
            // ignoring the actual lifetime ident
            matches!(other, GenericArgument::Lifetime(_))
        } else {
            self == other
        }
    }
}

impl NodeMatch for PathSegment {
    /// Compares both segments and returns true if `self` is similar to `seg_pat`, disregarding
    /// * any "turbofish" difference when there are angle bracket arguments
    /// * the arguments if `seg_pat` doesn't have any
    fn match_prefix(&self, seg_pat: &PathSegment) -> bool {
        self.ident == seg_pat.ident && match &seg_pat.arguments {
            PathArguments::None =>
                true, //matches!(seg_pat.arguments, PathArguments::None),
            PathArguments::AngleBracketed(ab_pat) => {
                if let PathArguments::AngleBracketed(ab) = &self.arguments {
                    // ignoring turbofish in colon2_token
                    ab.args.len() == ab_pat.args.len() &&
                        ab.args.iter().zip(&ab_pat.args).all(|(a, b)| a.match_prefix(b))
                } else {
                    false
                }
            }
            PathArguments::Parenthesized(p_pat) => {
                if let PathArguments::Parenthesized(p) = &self.arguments {
                    p == p_pat
                } else {
                    false
                }
            }
        }
    }
}

//==============================================================================
// Helper functions

/// Creates a string from a tokenizable item and removes the annoying spaces.
pub(crate) fn pathname<T: ToTokens>(path: &T) -> String {
    path.to_token_stream().to_string()
        .replace(" :: ", "::")
        .replace(" <", "<")
        .replace("< ", "<")
        .replace(" >", ">")
        .replace("> ", ">")
        .replace("& ", "&")
        .replace(", ", ",")
        .replace(") ", ")")
        .replace(" ;", ";")
        .replace("; ", ";")
}

/// Compares two type paths and, if `prefix` is a prefix of `full_path`, returns the number of
/// matching segments.
pub(crate) fn path_prefix_len(prefix: &Path, full_path: &Path) -> Option<usize> {
    let prefix_len = prefix.segments.len();
    if full_path.leading_colon == prefix.leading_colon && full_path.segments.len() >= prefix_len {
        for (seg_full, seg_prefix) in full_path.segments.iter().zip(&prefix.segments) {
            if !seg_full.match_prefix(seg_prefix) {
                return None;
            }
        }
        return Some(prefix_len)
    }
    None
}

/// Replaces the pattern `pat` with `repl` in `string`. Returns `Some(resulting string)` if
/// the string changed, None if there was no replacement.
pub(crate) fn replace_str(string: &str, pat: &str, repl: &str) -> Option<String> {
    if string.contains(pat) {
        Some(string.replace(pat, repl))
    } else {
        None
    }
}

