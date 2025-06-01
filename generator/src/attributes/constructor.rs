use std::{collections::VecDeque, fmt::Write};

use proc_macro2::Span;
use syn::{braced, parenthesized, punctuated::Punctuated, Ident, LitInt, Token};

use crate::attributes::{inline::GrammarInlineSource, path::GrammarPathSource};

use super::core::{GrammarDataSource, GrammarNode, GrammarSourceEmitter};

pub(super) use super::kw;
pub(crate) struct GrammarConstructorSource(String, Box<GrammarConstructor>);
impl GrammarDataSource for GrammarConstructorSource {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>,
    {
        let node = self.1;
        match *node {
            GrammarConstructor::Source(emitter) => emitter.emit(handler),
            other => {
                let mut buffer = String::new();
                other.build_source(self.0, &mut *handler, &mut buffer)?;
                Ok(())
            }
        }
    }
}

impl syn::parse::Parse for GrammarConstructorSource {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        input.parse::<kw::new>().unwrap();
        let inner;
        parenthesized!(inner in input);
        let ident = inner.parse::<Ident>()?;
        inner.parse::<Token![=]>()?;
        let constructor = inner.parse::<GrammarConstructor>()?;
        Ok(GrammarConstructorSource(
            ident.to_string(),
            Box::new(constructor),
        ))
    }
}

pub(crate) enum GrammarConstructor {
    Source(GrammarSourceEmitter),
    Sequence(Punctuated<GrammarConstructor, Token![,]>),
    Or(Punctuated<GrammarConstructor, Token![,]>),
    Repeat(Box<GrammarConstructor>, usize, usize),
    Token(GrammarConstructorToken),
    RootRule(GrammarNode),
    Wrapper(String, Box<GrammarConstructor>),
    Entry(Box<GrammarConstructor>),
}
#[derive(Default)]
struct ConstructionContext {
    separators: VecDeque<char>,
    new_sources: Vec<GrammarNode>,
}

#[derive(Clone, Copy)]
pub(crate) enum GrammarConstructorToken {
    GroupStart(char),
    GroupEnd,
    Separator,
    Repetition(usize, usize),
    Raw(&'static str),
}
impl GrammarConstructor {
    pub fn build_source<F>(
        self,
        root_rule: String,
        handler: &mut F,
        output: &mut dyn Write,
    ) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>,
    {
        pub fn build_source_node(
            context: &mut ConstructionContext,
            nodes: &mut VecDeque<GrammarConstructor>,
            output: &mut dyn Write,
        ) -> syn::Result<()> {
            if let Some(node) = nodes.pop_front() {
                match node {
                    GrammarConstructor::Source(emitter) => {
                        let mut multiple = false;
                        emitter.emit(&mut |node| {
                            if multiple {
                                nodes.push_front(GrammarConstructor::Token(
                                    GrammarConstructorToken::Separator,
                                ));
                            }
                            nodes.push_front(GrammarConstructor::RootRule(node));
                            multiple = true;
                            Ok(())
                        })?;
                    }
                    GrammarConstructor::Sequence(emitters) => {
                        nodes.push_front(GrammarConstructor::Token(
                            GrammarConstructorToken::GroupEnd,
                        ));
                        let mut iter = emitters.into_iter().peekable();
                        while let Some(emitter) = iter.next() {
                            nodes.push_front(emitter);
                            if iter.peek().is_some() {
                                nodes.push_front(GrammarConstructor::Token(
                                    GrammarConstructorToken::Separator,
                                ));
                            }
                        }
                        nodes.push_front(GrammarConstructor::Token(
                            GrammarConstructorToken::GroupStart('~'),
                        ));
                    }
                    GrammarConstructor::Or(emitters) => {
                        nodes.push_front(GrammarConstructor::Token(
                            GrammarConstructorToken::GroupEnd,
                        ));
                        let mut iter = emitters.into_iter().peekable();
                        while let Some(emitter) = iter.next() {
                            nodes.push_front(emitter);
                            if iter.peek().is_some() {
                                nodes.push_front(GrammarConstructor::Token(
                                    GrammarConstructorToken::Separator,
                                ));
                            }
                        }
                        nodes.push_front(GrammarConstructor::Token(
                            GrammarConstructorToken::GroupStart('|'),
                        ));
                    }
                    GrammarConstructor::Repeat(emitter, start, end) => {
                        nodes.push_front(GrammarConstructor::Token(
                            GrammarConstructorToken::Repetition(start, end),
                        ));

                        nodes.push_front(*emitter);
                    }
                    GrammarConstructor::RootRule(node) => {
                        let value = node.root_rule.clone().ok_or(syn::Error::new(
                            Span::call_site(),
                            "unable to determine root rule",
                        ))?;
                        context.new_sources.push(node);

                        output
                            .write_str(&value)
                            .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                    }
                    GrammarConstructor::Wrapper(root_rule, grammar_constructor) => {
                        let mut new_nodes = VecDeque::new();
                        new_nodes.push_front(*grammar_constructor);
                        let mut new_context = ConstructionContext::default();
                        let mut new_output = String::new();
                        while new_nodes.is_empty() == false {
                            build_source_node(&mut new_context, &mut new_nodes, &mut new_output)?;
                        }
                        context.new_sources.extend(new_context.new_sources);
                        let new_node = GrammarNode {
                            source: crate::GrammarSource::Inline(format!(
                                "{}={{{}}}",
                                &root_rule, new_output
                            )),
                            root_rule: Some(root_rule),
                        };
                        println!("New Node: {:?}", new_node);
                        nodes.push_front(GrammarConstructor::RootRule(new_node));
                    }
                    GrammarConstructor::Token(node) => match node {
                        GrammarConstructorToken::GroupStart(separator) => {
                            context.separators.push_front(separator);
                            output
                                .write_str("(")
                                .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                        }
                        GrammarConstructorToken::GroupEnd => {
                            context.separators.pop_front();
                            output
                                .write_str(")")
                                .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                        }
                        GrammarConstructorToken::Separator => {
                            if let Some(separator) = context.separators.front() {
                                output
                                    .write_char(*separator)
                                    .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                            }
                        }
                        GrammarConstructorToken::Repetition(start, end) => {
                            if start == end {
                                output
                                    .write_str("{")
                                    .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                                output
                                    .write_str(start.to_string().as_str())
                                    .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                                output
                                    .write_str("}")
                                    .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                            } else {
                                match (start, end) {
                                    (0, 1) => {
                                        output.write_str("?").map_err(|err| {
                                            syn::Error::new(Span::call_site(), err)
                                        })?;
                                    }
                                    (0, usize::MAX) => {
                                        output.write_str("*").map_err(|err| {
                                            syn::Error::new(Span::call_site(), err)
                                        })?;
                                    }
                                    (1, usize::MAX) => {
                                        output.write_str("+").map_err(|err| {
                                            syn::Error::new(Span::call_site(), err)
                                        })?;
                                    }
                                    (start, end) => {
                                        output.write_str("{").map_err(|err| {
                                            syn::Error::new(Span::call_site(), err)
                                        })?;
                                        output.write_str(start.to_string().as_str()).map_err(
                                            |err| syn::Error::new(Span::call_site(), err),
                                        )?;
                                        output.write_str(",").map_err(|err| {
                                            syn::Error::new(Span::call_site(), err)
                                        })?;
                                        output.write_str(end.to_string().as_str()).map_err(
                                            |err| syn::Error::new(Span::call_site(), err),
                                        )?;
                                        output.write_str("}").map_err(|err| {
                                            syn::Error::new(Span::call_site(), err)
                                        })?;
                                    }
                                }
                            }
                        }
                        GrammarConstructorToken::Raw(value) => {
                            output
                                .write_str(value)
                                .map_err(|err| syn::Error::new(Span::call_site(), err))?;
                        }
                    },
                    GrammarConstructor::Entry(grammar_constructor) => {
                        nodes.push_front(GrammarConstructor::Token(GrammarConstructorToken::Raw(
                            "EOI",
                        )));
                        nodes.push_front(GrammarConstructor::Token(GrammarConstructorToken::Raw(
                            "~",
                        )));
                        nodes.push_front(*grammar_constructor);
                        nodes.push_front(GrammarConstructor::Token(GrammarConstructorToken::Raw(
                            "~",
                        )));

                        nodes.push_front(GrammarConstructor::Token(GrammarConstructorToken::Raw(
                            "SOI",
                        )));
                    }
                }
            }
            Ok(())
        }
        let mut nodes = VecDeque::new();
        nodes.push_front(GrammarConstructor::Wrapper(root_rule, Box::new(self)));
        let mut context = ConstructionContext::default();
        while nodes.is_empty() == false {
            build_source_node(&mut context, &mut nodes, output)?;
        }
        for source in context.new_sources {
            handler(source)?;
        }
        Ok(())
    }
}

impl syn::parse::Parse for GrammarConstructor {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        fn parse_repetition(
            source: GrammarConstructor,
            input: syn::parse::ParseStream<'_>,
        ) -> syn::Result<GrammarConstructor> {
            if input.peek(Token![?]) {
                input.parse::<Token![?]>()?;
                Ok(GrammarConstructor::Repeat(Box::new(source), 0, 1))
            } else if input.peek(Token![*]) {
                input.parse::<Token![*]>()?;
                Ok(GrammarConstructor::Repeat(Box::new(source), 0, usize::MAX))
            } else if input.peek(Token![+]) {
                input.parse::<Token![+]>()?;
                Ok(GrammarConstructor::Repeat(Box::new(source), 1, usize::MAX))
            } else if input.peek(syn::token::Brace) {
                let inner;
                braced!(inner in input);
                let value1 = inner.parse::<LitInt>()?.base10_parse::<usize>()?;
                if inner.peek(Token![,]) {
                    inner.parse::<Token![,]>()?;
                    let value2 = inner.parse::<LitInt>()?.base10_parse::<usize>()?;
                    Ok(GrammarConstructor::Repeat(Box::new(source), value1, value2))
                } else {
                    Ok(GrammarConstructor::Repeat(Box::new(source), value1, value1))
                }
            } else {
                Ok(source)
            }
        }
        fn parse_data(input: syn::parse::ParseStream<'_>) -> syn::Result<GrammarConstructor> {
            if input.peek(kw::path) {
                Ok(parse_repetition(
                    GrammarConstructor::Source(GrammarSourceEmitter::Path(
                        input.parse::<GrammarPathSource>()?,
                    )),
                    input,
                )?)
            } else if input.peek(kw::inline) {
                Ok(parse_repetition(
                    GrammarConstructor::Source(GrammarSourceEmitter::Inline(
                        input.parse::<GrammarInlineSource>()?,
                    )),
                    input,
                )?)
            } else if input.peek(kw::entry) {
                input.parse::<kw::entry>()?;
                let inner;
                parenthesized!(inner in input);
                Ok(GrammarConstructor::Entry(Box::new(parse_data(&inner)?)))
            } else if input.peek(kw::or) {
                input.parse::<kw::or>()?;
                let inner;
                parenthesized!(inner in input);
                Ok(parse_repetition(
                    GrammarConstructor::Or(
                        inner.parse_terminated(GrammarConstructor::parse, Token![,])?,
                    ),
                    input,
                )?)
            } else if input.peek(kw::seq) {
                input.parse::<kw::seq>()?;
                let inner;
                parenthesized!(inner in input);
                Ok(parse_repetition(
                    GrammarConstructor::Sequence(
                        inner.parse_terminated(GrammarConstructor::parse, Token![,])?,
                    ),
                    input,
                )?)
            } else {
                Err(syn::Error::new(
                    Span::call_site(),
                    "invalid argument for grammar(...)",
                ))
            }
        }
        if input.peek(Ident) && input.peek2(Token![=]) {
            let root_rule = input.parse::<Ident>()?;
            input.parse::<Token![=]>()?;
            let next = parse_data(input)?;
            Ok(GrammarConstructor::Wrapper(
                root_rule.to_string(),
                Box::new(next),
            ))
        } else {
            parse_data(input)
        }
    }
}
