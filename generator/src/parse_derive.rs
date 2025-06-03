// pest. The Elegant Parser
// Copyright (c) 2018 Dragoș Tiselice
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

//! Types and helpers to parse the input of the derive macro.

use std::path::{Path, PathBuf};

use syn::{Attribute, DeriveInput, Expr, ExprLit, Generics, Ident, Lit, Meta};

use crate::attributes::{GrammarDataSource, GrammarSourceEmitter};

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum GrammarSource {
    File(PathBuf),
    Inline(String),
    RouteSet(Vec<String>),
}
pub(crate) struct GrammarInfo {
    pub sources: Vec<GrammarSource>,
    pub routes: Vec<(String, Vec<String>)>,
}

/// Parsed information of the derive and the attributes.
pub struct ParsedDerive {
    /// The identifier of the deriving struct, union, or enum.
    pub name: Ident,
    /// The generics of the deriving struct, union, or enum.
    pub generics: Generics,
    /// Indicates whether the 'non_exhaustive' attribute is added to the 'Rule' enum.
    pub non_exhaustive: bool,
}

pub(crate) fn parse_derive(ast: DeriveInput) -> (ParsedDerive, GrammarInfo) {
    let name = ast.ident;
    let generics = ast.generics;

    let grammar: Vec<&Attribute> = ast
        .attrs
        .iter()
        .filter(|attr| {
            let path = attr.meta.path();
            path.is_ident("grammar") || path.is_ident("grammar_inline")
        })
        .collect();

    if grammar.is_empty() {
        panic!("a grammar file needs to be provided with the #[grammar = \"PATH\"] or #[grammar_inline = \"GRAMMAR CONTENTS\"] attribute");
    }

    let mut grammar_sources = Vec::with_capacity(grammar.len());
    let mut routes = Vec::new();
    parse_attributes(grammar, &mut grammar_sources, &mut routes);

    let non_exhaustive = ast
        .attrs
        .iter()
        .any(|attr| attr.meta.path().is_ident("non_exhaustive"));

    (
        ParsedDerive {
            name,
            generics,
            non_exhaustive,
        },
        GrammarInfo {
            sources: grammar_sources,
            routes: routes,
        },
    )
}
fn parse_attributes(
    attrs: Vec<&Attribute>,
    grammars: &mut Vec<GrammarSource>,
    routes: &mut Vec<(String, Vec<String>)>,
) {
    for attr in attrs {
        match &attr.meta {
            Meta::List(meta) => {
                if meta.path.is_ident("grammar") {
                    let source = meta.parse_args::<GrammarSourceEmitter>().unwrap();
                    source
                        .emit(&mut |node| {
                            if let GrammarSource::RouteSet(node_routes) = node.source {
                                if let Some(root_rule) = node.root_rule {
                                    routes.push((root_rule, node_routes));
                                }
                            } else {
                                grammars.push(node.source);
                            }

                            Ok(())
                        })
                        .unwrap();
                }
            }
            Meta::NameValue(meta) => match &meta.value {
                Expr::Lit(ExprLit {
                    lit: Lit::Str(string),
                    ..
                }) => {
                    if meta.path.is_ident("grammar") {
                        grammars.push(GrammarSource::File(
                            Path::new(&string.value()).to_path_buf(),
                        ));
                    } else {
                        grammars.push(GrammarSource::Inline(string.value()))
                    }
                }
                _ => panic!("grammar attribute must be a string"),
            },
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::GrammarInfo;

    use super::parse_derive;
    use super::GrammarSource;

    #[test]
    fn derive_inline_file() {
        let definition = "
            #[other_attr]
            #[grammar_inline = \"GRAMMAR\"]
            pub struct MyParser<'a, T>;
        ";
        let ast = syn::parse_str(definition).unwrap();
        let (_, info) = parse_derive(ast);
        assert_eq!(info.sources, [GrammarSource::Inline("GRAMMAR".to_string())]);
    }

    #[test]
    fn derive_ok() {
        let definition = "
            #[other_attr]
            #[grammar = \"myfile.pest\"]
            pub struct MyParser<'a, T>;
        ";
        let ast = syn::parse_str(definition).unwrap();
        let (parsed_derive, info) = parse_derive(ast);
        assert_eq!(
            info.sources,
            [GrammarSource::File(Path::new("myfile.pest").to_path_buf())]
        );
        assert!(!parsed_derive.non_exhaustive);
    }

    #[test]
    fn derive_multiple_grammars() {
        let definition = "
            #[other_attr]
            #[grammar = \"myfile1.pest\"]
            #[grammar = \"myfile2.pest\"]
            pub struct MyParser<'a, T>;
        ";
        let ast = syn::parse_str(definition).unwrap();
        let (_, info) = parse_derive(ast);
        assert_eq!(
            info.sources,
            [
                GrammarSource::File(Path::new("myfile1.pest").to_path_buf()),
                GrammarSource::File(Path::new("myfile2.pest").to_path_buf())
            ]
        );
    }

    #[test]
    fn derive_nonexhaustive() {
        let definition = "
            #[non_exhaustive]
            #[grammar = \"myfile.pest\"]
            pub struct MyParser<'a, T>;
        ";
        let ast = syn::parse_str(definition).unwrap();
        let (parsed_derive, info) = parse_derive(ast);
        assert_eq!(
            info.sources,
            [GrammarSource::File(Path::new("myfile.pest").to_path_buf())]
        );
        assert!(parsed_derive.non_exhaustive);
    }

    #[test]
    #[should_panic(expected = "grammar attribute must be a string")]
    fn derive_wrong_arg() {
        let definition = "
            #[other_attr]
            #[grammar = 1]
            pub struct MyParser<'a, T>;
        ";
        let ast = syn::parse_str(definition).unwrap();
        parse_derive(ast);
    }

    #[test]
    #[should_panic(
        expected = "a grammar file needs to be provided with the #[grammar = \"PATH\"] or #[grammar_inline = \"GRAMMAR CONTENTS\"] attribute"
    )]
    fn derive_no_grammar() {
        let definition = "
            #[other_attr]
            pub struct MyParser<'a, T>;
        ";
        let ast = syn::parse_str(definition).unwrap();
        parse_derive(ast);
    }
}
