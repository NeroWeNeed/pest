use core::fmt;
use std::{fmt::Write, usize};

use proc_macro2::Span;
use syn::{
    braced, parenthesized,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    token::{Brace, Paren},
    Ident, LitChar, LitInt, LitStr, Token,
};

use super::{path::GrammarPathSource, GrammarDataSource, GrammarNode};

trait RuleStep {
    fn step<F>(&self, handler: &mut F, output: &mut dyn Write) -> fmt::Result
    where
        F: FnMut(RuleEvent);
}
enum RuleEvent {
    Node(GrammarNode),
    RootRule(String),
}
enum Node {
    Sequence(Punctuated<Node, Token![~]>),
    OrderedChoice(Punctuated<Node, Token![|]>),
    Repetition(Box<Node>, usize, usize),
    Predicate(Box<Node>, PredicateType),
    String(LitStr),
    CharacterRange(LitChar, LitChar),
    RuleRef(String, bool),
    Collection(Vec<Node>),
    Emission(GrammarNode),
    Empty,
}
fn handle_rule_fn(ident: Ident, input: ParseStream<'_>) -> syn::Result<Node> {
    match ident.to_string().as_str() {
        "path" => {
            let value = GrammarPathSource(input.parse::<LitStr>()?.value());
            if input.peek2(LitChar) {
                input.parse::<Token![,]>()?;
                let delimiter = input.parse::<LitChar>()?.value();
                let mut output = Vec::new();

                if delimiter == '|' {
                    let mut punctuated: Punctuated<Node, Token![|]> = Punctuated::new();
                    value.emit(&mut |node| {
                        if let Some(root_rule) = node.root_rule.clone() {
                            output.push(Node::Emission(node));
                            punctuated.push_value(Node::RuleRef(root_rule, true));
                        } else {
                            output.push(Node::Emission(node));
                        }
                        Ok(())
                    })?;
                    output.push(Node::OrderedChoice(punctuated));
                    Ok(Node::Collection(output))
                } else if delimiter == '~' {
                    let mut punctuated: Punctuated<Node, Token![~]> = Punctuated::new();
                    value.emit(&mut |node| {
                        if let Some(root_rule) = node.root_rule.clone() {
                            output.push(Node::Emission(node));
                            punctuated.push_value(Node::RuleRef(root_rule, true));
                        } else {
                            output.push(Node::Emission(node));
                        }
                        Ok(())
                    })?;
                    output.push(Node::Sequence(punctuated));
                    Ok(Node::Collection(output))
                } else {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "invalid delimiter for path",
                    ));
                }
            } else {
                let mut output = None;
                value.emit(&mut |node| {
                    if output.is_none() {
                        output = Some(node);
                        Ok(())
                    } else {
                        Err(syn::Error::new(
                            Span::call_site(),
                            "path() requires delimiter when a directory is specified",
                        ))
                    }
                })?;
                if let Some(node) = output {
                    if let Some(root_rule) = &node.root_rule.clone() {
                        Ok(Node::Collection(vec![
                            Node::Emission(node),
                            Node::RuleRef(root_rule.clone(), true),
                        ]))
                    } else {
                        Ok(Node::Emission(node))
                    }
                } else {
                    Ok(Node::Empty)
                }
            }
        }
        _ => {
            return Err(syn::Error::new(
                Span::call_site(),
                "path() requires delimiter when a directory is specified",
            ));
        }
    }
}

impl RuleStep for Node {
    fn step<F>(&self, handler: &mut F, output: &mut dyn Write) -> fmt::Result
    where
        F: FnMut(RuleEvent),
    {
        match self {
            Node::Sequence(punctuated) => {
                if punctuated.len() > 1 {
                    output.write_char('(')?;

                    let mut iter = punctuated.iter().peekable();
                    while let Some(node) = iter.next() {
                        node.step(handler, output)?;
                        if iter.peek().is_some() {
                            output.write_char('~')?;
                        }
                    }
                    output.write_char(')')?;
                } else {
                    let mut iter = punctuated.iter().peekable();
                    while let Some(node) = iter.next() {
                        node.step(handler, output)?;
                        if iter.peek().is_some() {
                            output.write_char('~')?;
                        }
                    }
                }
            }
            Node::OrderedChoice(punctuated) => {
                if punctuated.len() > 1 {
                    output.write_char('(')?;

                    let mut iter = punctuated.iter().peekable();
                    while let Some(node) = iter.next() {
                        node.step(handler, output)?;
                        if iter.peek().is_some() {
                            output.write_char('|')?;
                        }
                    }
                    output.write_char(')')?;
                } else {
                    let mut iter = punctuated.iter().peekable();
                    while let Some(node) = iter.next() {
                        node.step(handler, output)?;
                        if iter.peek().is_some() {
                            output.write_char('|')?;
                        }
                    }
                }
            }
            Node::Repetition(node, start, end) => {
                node.step(handler, output)?;
                if start == end {
                    output.write_fmt(format_args!("{{{}}}", start))?;
                } else {
                    match (*start, *end) {
                        (0, 1) => {
                            output.write_char('?')?;
                        }
                        (0, usize::MAX) => {
                            output.write_char('*')?;
                        }
                        (1, usize::MAX) => {
                            output.write_char('+')?;
                        }
                        (start, end) => {
                            output.write_fmt(format_args!("{{{},{}}}", start, end))?;
                        }
                    }
                }
            }
            Node::Predicate(node, predicate_type) => {
                match predicate_type {
                    PredicateType::Positive => output.write_char('&'),
                    PredicateType::Negative => output.write_char('!'),
                    PredicateType::Casing => output.write_char('^'),
                }?;
                node.step(handler, output)?;
            }
            Node::String(lit_str) => {
                output.write_fmt(format_args!("\"{}\"", lit_str.value()))?;
            }
            Node::CharacterRange(start, end) => {
                output.write_fmt(format_args!("'{}'..'{}'", start.value(), end.value()))?;
            }
            Node::RuleRef(ident, expose) => {
                output.write_fmt(format_args!("{}", ident))?;
                if *expose {
                    handler(RuleEvent::RootRule(ident.to_string()))
                }
            }
            Node::Empty => {}
            Node::Collection(nodes) => {
                for node in nodes {
                    node.step(handler, output)?;
                }
            }
            Node::Emission(grammar_node) => handler(RuleEvent::Node(grammar_node.clone())),
        }
        Ok(())
    }
}
impl Parse for Node {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        fn parse_data<'b>(input: ParseStream<'_>) -> syn::Result<Node> {
            if input.peek(Token![&]) {
                input.parse::<Token![&]>()?;
                Ok(Node::Predicate(
                    Box::new(input.parse::<Node>()?),
                    PredicateType::Positive,
                ))
            } else if input.peek(Token![!]) {
                input.parse::<Token![!]>()?;
                Ok(Node::Predicate(
                    Box::new(input.parse::<Node>()?),
                    PredicateType::Negative,
                ))
            } else if input.peek(LitStr) {
                Ok(Node::String(input.parse::<LitStr>()?))
            } else if input.peek(Token![^]) && input.peek2(LitStr) {
                input.parse::<Token![^]>()?;
                Ok(Node::Predicate(
                    Box::new(Node::String(input.parse::<LitStr>()?)),
                    PredicateType::Casing,
                ))
            } else if input.peek(Ident) {
                let ident = input.parse::<Ident>()?;

                if input.peek(Paren) {
                    let inner;
                    parenthesized!(inner in input);
                    handle_rule_fn(ident, &inner)
                } else {
                    Ok(Node::RuleRef(ident.to_string(), false))
                }
            } else if input.peek(LitChar) {
                let start = input.parse::<LitChar>()?;
                input.parse::<Token![..]>()?;
                let end = input.parse::<LitChar>()?;
                Ok(Node::CharacterRange(start, end))
            } else if input.peek(Paren) {
                let inner;
                parenthesized!(inner in input);
                if inner.is_empty() {
                    return Ok(Node::Empty);
                }
                let first_item = inner.parse::<Node>()?;
                if inner.is_empty() {
                    return Ok(first_item);
                }
                if inner.peek(Token![|]) {
                    inner.parse::<Token![|]>()?;
                    let next = inner.parse_terminated(Node::parse, Token![|])?;
                    let mut result = Punctuated::new();
                    result.push_value(first_item);
                    result.extend(next);
                    return Ok(Node::OrderedChoice(result));
                } else if inner.peek(Token![~]) {
                    inner.parse::<Token![~]>()?;
                    let next = inner.parse_terminated(Node::parse, Token![~])?;
                    let mut result = Punctuated::new();
                    result.push_value(first_item);
                    result.extend(next);
                    return Ok(Node::Sequence(result));
                } else {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "invalid group delimiter",
                    ));
                }
            } else {
                Err(syn::Error::new(
                    Span::call_site(),
                    "invalid token for grammar",
                ))
            }
        }
        fn parse_footer(node: Node, input: ParseStream<'_>) -> syn::Result<Node> {
            if input.peek(Token![*]) {
                input.parse::<Token![*]>()?;
                Ok(Node::Repetition(Box::new(node), 0, usize::MAX))
            } else if input.peek(Token![*]) {
                input.parse::<Token![+]>()?;
                Ok(Node::Repetition(Box::new(node), 1, usize::MAX))
            } else if input.peek(Token![?]) {
                input.parse::<Token![*]>()?;
                Ok(Node::Repetition(Box::new(node), 0, 1))
            } else if input.peek(Brace) {
                let inner;
                braced!(inner in input);
                let start = inner.parse::<LitInt>()?.base10_parse()?;
                if inner.peek(Token![,]) {
                    inner.parse::<Token![,]>()?;
                    let end = inner.parse::<LitInt>()?.base10_parse()?;
                    Ok(Node::Repetition(Box::new(node), start, end))
                } else if inner.is_empty() {
                    Ok(Node::Repetition(Box::new(node), start, start))
                } else {
                    Err(syn::Error::new(
                        Span::call_site(),
                        "invalid token for grammar",
                    ))
                }
            } else {
                Ok(node)
            }
        }
        parse_footer(parse_data(input)?, input)
    }
}

#[derive(Debug, Clone, Copy)]
enum PredicateType {
    Positive,
    Negative,
    Casing,
}
#[derive(Default, Debug, Clone, Copy)]
enum RuleType {
    #[default]
    Regular,
    Atomic,
    CompoundAtomic,
    Silent,
    NonAtomic,
}
impl Parse for RuleType {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if input.peek(Token![@]) {
            input.parse::<Token![@]>()?;
            Ok(Self::Atomic)
        } else if input.peek(Token![$]) {
            input.parse::<Token![$]>()?;
            Ok(Self::CompoundAtomic)
        } else if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            Ok(Self::Silent)
        } else if input.peek(Token![!]) {
            input.parse::<Token![!]>()?;
            Ok(Self::NonAtomic)
        } else {
            Ok(Self::Regular)
        }
    }
}
struct RuleDefinitionContent {
    ty: RuleType,
    content: Node,
}
impl RuleStep for RuleDefinitionContent {
    fn step<F>(&self, handler: &mut F, output: &mut dyn Write) -> fmt::Result
    where
        F: FnMut(RuleEvent),
    {
        match self.ty {
            RuleType::Regular => {}
            RuleType::Atomic => output.write_char('@')?,
            RuleType::CompoundAtomic => output.write_char('$')?,
            RuleType::Silent => output.write_char('_')?,
            RuleType::NonAtomic => output.write_char('!')?,
        };
        output.write_char('{')?;
        self.content.step(handler, output)?;
        output.write_char('}')?;
        Ok(())
    }
}

impl Parse for RuleDefinitionContent {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let rule_type = input.parse::<RuleType>()?;
        let inner;
        braced!(inner in input);
        if inner.is_empty() {
            return Ok(Self {
                ty: rule_type,
                content: Node::Empty,
            });
        }
        let first_item = inner.parse::<Node>()?;
        if inner.is_empty() {
            return Ok(Self {
                ty: rule_type,
                content: first_item,
            });
        }
        if inner.peek(Token![|]) {
            inner.parse::<Token![|]>()?;
            let next = inner.parse_terminated(Node::parse, Token![|])?;
            let mut result = Punctuated::new();
            result.push_value(first_item);
            result.extend(next);
            return Ok(Self {
                ty: rule_type,
                content: Node::OrderedChoice(result),
            });
        } else if inner.peek(Token![~]) {
            inner.parse::<Token![~]>()?;
            let next = inner.parse_terminated(Node::parse, Token![~])?;
            let mut result = Punctuated::new();
            result.push_value(first_item);
            result.extend(next);
            return Ok(Self {
                ty: rule_type,
                content: Node::Sequence(result),
            });
        } else {
            return Err(syn::Error::new(
                Span::call_site(),
                "invalid group delimiter",
            ));
        }
    }
}
pub struct RuleDefinition {
    name: Ident,
    content: RuleDefinitionContent,
}
impl RuleStep for RuleDefinition {
    fn step<F>(&self, handler: &mut F, output: &mut dyn Write) -> fmt::Result
    where
        F: FnMut(RuleEvent),
    {
        output.write_str(self.name.to_string().as_str())?;
        output.write_char('=')?;
        self.content.step(handler, output)
    }
}
impl Parse for RuleDefinition {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name = input.parse::<Ident>()?;
        input.parse::<Token![=]>()?;
        Ok(Self {
            name: name,
            content: input.parse::<RuleDefinitionContent>()?,
        })
    }
}

impl GrammarDataSource for RuleDefinition {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>,
    {
        let mut output = String::new();
        let mut sources = Vec::new();
        let mut roots = Vec::new();
        self.step(
            &mut |evt| match evt {
                RuleEvent::Node(grammar_node) => {
                    sources.push(grammar_node);
                }
                RuleEvent::RootRule(ident) => {
                    roots.push(ident.to_string());
                }
            },
            &mut output,
        )
        .map_err(|err| syn::Error::new(Span::call_site(), err))?;
        for source in sources {
            handler(source)?;
        }
        if !roots.is_empty() {
            handler(GrammarNode {
                source: crate::GrammarSource::RouteSet(roots),
                root_rule: Some(self.name.to_string()),
            })?;
        }
        println!("Out: {output}");
        handler(GrammarNode {
            source: crate::GrammarSource::Inline(output),
            root_rule: Some(self.name.to_string()),
        })?;
        Ok(())
    }
}
