// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Based on riscv-rt

#![deny(warnings)]

extern crate proc_macro;
extern crate rand;
#[macro_use]
extern crate quote;
extern crate core;
extern crate proc_macro2;
#[macro_use]
extern crate syn;

use proc_macro2::Span;
use rand::Rng;
use rand::SeedableRng;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};
use syn::{parse, spanned::Spanned, Ident, ItemFn, ReturnType, Type, Visibility};

static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn entry(args: TokenStream, input: TokenStream) -> TokenStream {
    let f = parse_macro_input!(input as ItemFn);

    // check the function signature
    let valid_signature = f.sig.constness.is_none()
        && f.sig.asyncness.is_none()
        && f.vis == Visibility::Inherited
        && f.sig.abi.is_none()
        && f.sig.inputs.is_empty()
        && f.sig.generics.params.is_empty()
        && f.sig.generics.where_clause.is_none()
        && f.sig.variadic.is_none()
        && match f.sig.output {
            // TODO: figure out how to check for u32 return type
            ReturnType::Default => false,
            ReturnType::Type(_, ref ty) => match **ty {
                // Type::Array(_) => true,
                // Type::BareFn(_) => true,
                // Type::Group(_) => true,
                // Type::ImplTrait(_) => true,
                // Type::Infer(_) => true,
                // Type::Macro(_) => true,
                // Type::Never(_) => true,
                // Type::Paren(_) => true,
                Type::Path(_) => true,
                // Type::Ptr(_) => true,
                // Type::Reference(_) => true,
                // Type::Slice(_) => true,
                // Type::TraitObject(_) => true,
                // Type::Tuple(_) => true,
                // Type::Verbatim(_) => true,
                _ => false,
            },
        };

    if !valid_signature {
        return parse::Error::new(
            f.span(),
            "`#[entry]` function must have signature `[unsafe] fn() -> usize`",
        )
        .to_compile_error()
        .into();
    }

    if !args.is_empty() {
        return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
            .to_compile_error()
            .into();
    }

    // XXX should we blacklist other attributes?
    let attrs = f.attrs;
    let unsafety = f.sig.unsafety;
    let hash = random_ident();
    let stmts = f.block.stmts;

    quote!(
        #[export_name = "main"]
        #(#attrs)*
        pub #unsafety fn #hash() -> u32 {
            #(#stmts)*
        }
    )
    .into()
}



// Creates a random identifier
fn random_ident() -> Ident {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();

    let count: u64 = CALL_COUNT.fetch_add(1, Ordering::SeqCst) as u64;
    let mut seed: [u8; 16] = [0; 16];

    for (i, v) in seed.iter_mut().take(8).enumerate() {
        *v = ((secs >> (i * 8)) & 0xFF) as u8
    }

    for (i, v) in seed.iter_mut().skip(8).enumerate() {
        *v = ((count >> (i * 8)) & 0xFF) as u8
    }

    let mut rng = rand::rngs::SmallRng::from_seed(seed);
    Ident::new(
        &(0..16)
            .map(|i| {
                if i == 0 || rng.gen() {
                    ('a' as u8 + rng.gen::<u8>() % 25) as char
                } else {
                    ('0' as u8 + rng.gen::<u8>() % 10) as char
                }
            })
            .collect::<String>(),
        Span::call_site(),
    )
}
