use proc_macro2::Span;
use syn::{Ident, LitStr, Token};

use crate::GrammarSource;

use super::{constructor::RuleDefinition, inline::GrammarInlineSource, path::GrammarPathSource};
pub(super) mod kw {
    syn::custom_keyword!(path);
    syn::custom_keyword!(inline);
    syn::custom_keyword!(new);
    syn::custom_keyword!(or);
    syn::custom_keyword!(seq);
    syn::custom_keyword!(entry);
    syn::custom_keyword!(route);
}

pub trait GrammarDataSource {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>;
}
#[derive(Debug, Clone)]
pub(crate) struct GrammarNode {
    pub source: GrammarSource,
    pub root_rule: Option<String>,
}
pub(crate) enum GrammarSourceEmitter {
    Path(GrammarPathSource),
    Inline(GrammarInlineSource),
    Definition(RuleDefinition),
}

impl GrammarDataSource for GrammarSourceEmitter {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>,
    {
        match self {
            GrammarSourceEmitter::Path(source) => source.emit(handler),
            GrammarSourceEmitter::Inline(source) => source.emit(handler),
            GrammarSourceEmitter::Definition(source) => source.emit(handler),
        }
    }
}

impl syn::parse::Parse for GrammarSourceEmitter {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        if input.peek(kw::path) {
            Ok(GrammarSourceEmitter::Path(
                input.parse::<GrammarPathSource>()?,
            ))
        } else if input.peek(LitStr) {
            Ok(GrammarSourceEmitter::Inline(
                input.parse::<GrammarInlineSource>()?,
            ))
        } else if input.peek(Ident) && input.peek2(Token![=]) {
            Ok(GrammarSourceEmitter::Definition(
                input.parse::<RuleDefinition>()?,
            ))
        } else {
            Err(syn::Error::new(
                Span::call_site(),
                "invalid argument for grammar(...)",
            ))
        }
    }
}
