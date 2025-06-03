use std::{
    env,
    path::{Path, PathBuf},
};

use proc_macro2::Span;
use syn::{parenthesized, LitStr};

use super::core::{GrammarDataSource, GrammarNode};
pub(super) use super::kw;

pub(crate) struct GrammarPathSource(pub String);
impl GrammarDataSource for GrammarPathSource {
    fn emit<F>(self, handler: &mut F) -> syn::Result<()>
    where
        F: FnMut(GrammarNode) -> syn::Result<()>,
    {
        fn emit_path<F>(path: PathBuf, handler: &mut F) -> syn::Result<()>
        where
            F: FnMut(GrammarNode) -> syn::Result<()>,
        {
            let root_rule = path
                .file_stem()
                .and_then(|value| value.to_os_string().into_string().ok());
            handler(GrammarNode {
                source: crate::GrammarSource::File(path),
                root_rule,
            })?;
            Ok(())
        }
        let path = Path::new(&self.0);
        let root = env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".into());
        let path = std::path::absolute(Path::new(&root).join(path))
            .map_err(|err| syn::Error::new(Span::call_site(), err))?;
        if path.is_file() {
            emit_path(path, handler)?;
        } else if path.is_dir() {
            for path in path.read_dir().unwrap() {
                let path = path.unwrap().path();
                if path.is_file() {
                    let path = if Path::new(&root).join(&path).exists() {
                        Path::new(&root).join(path)
                    } else {
                        Path::new(&root).join("src/").join(&path)
                    };
                    emit_path(path, handler)?;
                }
            }
        }
        Ok(())
    }
}

impl syn::parse::Parse for GrammarPathSource {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        input.parse::<kw::path>().unwrap();
        let inner;
        parenthesized!(inner in input);
        let inner = inner.parse::<LitStr>()?.value();
        Ok(GrammarPathSource(inner))
    }
}
