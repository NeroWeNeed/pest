use proc_macro2::Span;

use crate::GrammarSource;

use super::{
    constructor::GrammarConstructorSource, inline::GrammarInlineSource, path::GrammarPathSource,
};
pub(super) mod kw {
    syn::custom_keyword!(path);
    syn::custom_keyword!(inline);
    syn::custom_keyword!(new);
    syn::custom_keyword!(or);
    syn::custom_keyword!(seq);
    syn::custom_keyword!(optional);
    syn::custom_keyword!(zeroOrMore);
    syn::custom_keyword!(oneOrMore);
    syn::custom_keyword!(repeat);
    syn::custom_keyword!(entry);
}

pub trait GrammarDataSource {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>;
}
#[derive(Debug)]
pub(crate) struct GrammarNode {
    pub source: GrammarSource,
    pub root_rule: Option<String>,
}
pub(crate) enum GrammarSourceEmitter {
    Path(GrammarPathSource),
    Inline(GrammarInlineSource),
    Constructor(GrammarConstructorSource),
}

impl GrammarDataSource for GrammarSourceEmitter {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>,
    {
        match self {
            GrammarSourceEmitter::Path(source) => source.emit(handler),
            GrammarSourceEmitter::Inline(source) => source.emit(handler),
            GrammarSourceEmitter::Constructor(source) => source.emit(handler),
        }
    }
}

impl syn::parse::Parse for GrammarSourceEmitter {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        if input.peek(kw::path) {
            Ok(GrammarSourceEmitter::Path(
                input.parse::<GrammarPathSource>()?,
            ))
        } else if input.peek(kw::inline) {
            Ok(GrammarSourceEmitter::Inline(
                input.parse::<GrammarInlineSource>()?,
            ))
        } else if input.peek(kw::new) {
            Ok(GrammarSourceEmitter::Constructor(
                input.parse::<GrammarConstructorSource>()?,
            ))
        } else {
            Err(syn::Error::new(
                Span::call_site(),
                "invalid argument for grammar(...)",
            ))
        }
    }
}
