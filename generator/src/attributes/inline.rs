use syn::{parenthesized, Ident, LitStr, Token};

use crate::{attributes::kw, GrammarSource};

use super::core::{GrammarDataSource, GrammarNode};

pub(crate) struct GrammarInlineSource(Option<String>, String);
impl GrammarDataSource for GrammarInlineSource {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>,
    {
        handler(GrammarNode {
            source: GrammarSource::Inline(self.1),
            root_rule: self.0,
        })
    }
}
impl syn::parse::Parse for GrammarInlineSource {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        input.parse::<kw::inline>().unwrap();
        let inner;
        parenthesized!(inner in input);
        let root = if inner.peek(Ident) {
            let ident = inner.parse::<Ident>()?;
            inner.parse::<Token![=]>()?;
            Some(ident.to_string())
        } else {
            None
        };
        let inner = inner.parse::<LitStr>()?.value();
        Ok(GrammarInlineSource(root, inner))
    }
}
