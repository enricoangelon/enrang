//! The token tables against SPEC 2, and `split_token`.

use std::collections::BTreeSet;

use enrang_base::{BytePos, Span};
use enrang_diag::{Code, Milestone, Owner, Phase};
use enrang_syntax::{Contextual, Keyword, Punct, Reserved, Token, TokenKind};
use enrang_testkit::Harness;

use crate::support::{backticked, doc, section, terminals};

fn lexical_grammar() -> &'static str {
    section(doc("SPEC.md"), "## 2. Lexical grammar")
}

/// Each reserved word that a code's title in SPEC 13.2 quotes, with that code.
fn titled_words() -> Vec<(Reserved, Code)> {
    let mut found = Vec::new();
    for &word in Reserved::ALL {
        let quoted = format!("`{}`", word.as_str());
        let titled: Vec<Code> = Code::ALL
            .iter()
            .copied()
            .filter(|code| code.owner() == Owner::Syntax)
            .filter(|code| code.title().contains(&quoted))
            .collect();
        assert!(titled.len() <= 1, "{word:?}: {titled:?}");
        found.extend(titled.first().map(|&code| (word, code)));
    }
    found
}

/// Each reserved word in the "Feature seen" column of SPEC 16's table, with the code
/// of its row.
fn deferred_words() -> Vec<(Reserved, Code)> {
    let table = section(doc("SPEC.md"), "## 16. Deferred features");
    let mut found = Vec::new();
    for row in table.lines().filter(|line| line.starts_with("| EN")) {
        let mut cells = row.split(" | ");
        let code = cells.next().expect("a code cell").trim_start_matches("| ");
        let code = Code::from_name(code).unwrap_or_else(|| panic!("{code} is no code"));
        let seen = cells.next().expect("a feature cell");
        for word in backticked(seen) {
            found.extend(Reserved::from_name(&word).map(|word| (word, code)));
        }
    }
    found
}

/// The reserved words no title of SPEC 13.2 and no row of SPEC 16 names, with the
/// code each gets and where that comes from.
const UNNAMED: &[(Reserved, Code, &str)] = &[
    // SPEC 3.1, `ItemVis`: "missing: EN0226, which also turns `export` into
    // `public`"; and 4.12: "`export` gets the same code with a fix-it to `public`".
    (
        Reserved::Export,
        Code::EN0226,
        "turns `export` into `public`",
    ),
    // No SPEC line names them (a doc gap): `case` belongs to `switch`, so EN0209,
    // and `finally` to `try`, so EN0207, as the plan's code table says.
    (Reserved::Case, Code::EN0209, ""),
    (Reserved::Finally, Code::EN0207, ""),
];

fn spellings<T: Copy>(all: &[T], as_str: fn(T) -> &'static str) -> Vec<String> {
    all.iter().map(|&word| as_str(word).to_owned()).collect()
}

/// The tokens a sentence lists in backticks between two phrases of it.
fn listed_between(text: &str, from: &str, to: &str) -> Vec<String> {
    let start = text.find(from).unwrap_or_else(|| panic!("no {from:?}")) + from.len();
    let len = text[start..]
        .find(to)
        .unwrap_or_else(|| panic!("no {to:?} after {from:?}"));
    backticked(&text[start..start + len])
}

pub fn register(h: &mut Harness) {
    h.case("tokens/keywords are SPEC 2's, in order", || {
        let spec = terminals(lexical_grammar(), "Keyword");
        assert_eq!(spellings(Keyword::ALL, Keyword::as_str), spec);
    });
    h.case("tokens/contextual words are SPEC 2's, in order", || {
        let spec = terminals(lexical_grammar(), "Contextual");
        assert_eq!(spellings(Contextual::ALL, Contextual::as_str), spec);
    });
    h.case("tokens/reserved words are SPEC 2's, in order", || {
        let spec = terminals(lexical_grammar(), "Reserved");
        assert_eq!(spellings(Reserved::ALL, Reserved::as_str), spec);
    });
    h.case("tokens/punctuators are SPEC 2's, in order", || {
        let spec = terminals(lexical_grammar(), "Punct");
        assert_eq!(spellings(Punct::ALL, Punct::as_str), spec);
    });
    h.case("tokens/each word and punctuator is spelled once", || {
        let mut seen = BTreeSet::new();
        let words = spellings(Keyword::ALL, Keyword::as_str)
            .into_iter()
            .chain(spellings(Contextual::ALL, Contextual::as_str))
            .chain(spellings(Reserved::ALL, Reserved::as_str))
            .chain(spellings(Punct::ALL, Punct::as_str));
        for word in words {
            assert!(seen.insert(word.clone()), "{word} is in two tables");
        }
    });
    h.case(
        "tokens/from_name finds each spelling and nothing else",
        || {
            for &k in Keyword::ALL {
                assert_eq!(Keyword::from_name(k.as_str()), Some(k));
            }
            for &c in Contextual::ALL {
                assert_eq!(Contextual::from_name(c.as_str()), Some(c));
            }
            for &r in Reserved::ALL {
                assert_eq!(Reserved::from_name(r.as_str()), Some(r));
            }
            for &p in Punct::ALL {
                assert_eq!(Punct::from_name(p.as_str()), Some(p));
            }
            for word in ["", "Class", "get", "sizeOf", "Ok", "#", "??=", "**="] {
                assert_eq!(Keyword::from_name(word), None, "{word}");
                assert_eq!(Contextual::from_name(word), None, "{word}");
                assert_eq!(Reserved::from_name(word), None, "{word}");
                assert_eq!(Punct::from_name(word), None, "{word}");
            }
        },
    );
    h.case(
        "tokens/every reserved word has a phase 1 syntax code of M1",
        || {
            for &word in Reserved::ALL {
                let code = word.code();
                assert_eq!(code.phase(), Phase::Syntax, "{word:?}");
                assert_eq!(code.owner(), Owner::Syntax, "{word:?}");
                assert_eq!(code.since(), Milestone::M1, "{word:?}");
            }
        },
    );
    h.case(
        "tokens/reserved words named by a code's title get that code",
        || {
            let titled = titled_words();
            assert_eq!(titled.len(), 14, "{titled:?}");
            for (word, code) in titled {
                assert_eq!(word.code(), code, "{word:?}");
            }
        },
    );
    h.case(
        "tokens/reserved words of SPEC 16's Feature seen column get that row's code",
        || {
            let deferred = deferred_words();
            let words: Vec<Reserved> = deferred.iter().map(|&(word, _)| word).collect();
            let expected = [
                Reserved::Async,
                Reserved::Await,
                Reserved::Yield,
                Reserved::Keyof,
            ];
            assert_eq!(words, expected);
            for (word, code) in deferred {
                assert_eq!(word.code(), code, "{word:?}");
            }
        },
    );
    h.case("tokens/the reserved words no title names", || {
        let spec = doc("SPEC.md");
        for &(word, code, quote) in UNNAMED {
            assert_eq!(word.code(), code, "{word:?}");
            assert!(spec.contains(quote), "SPEC no longer says {quote:?}");
        }
        let item_vis = spec
            .lines()
            .find(|line| line.starts_with("ItemVis"))
            .expect("SPEC 3.1 has ItemVis");
        assert!(item_vis.contains("EN0226") && item_vis.contains("`export`"));
    });
    h.case(
        "tokens/every reserved word's code comes from exactly one place",
        || {
            let mut named: Vec<Reserved> = titled_words()
                .into_iter()
                .chain(deferred_words())
                .map(|(word, _)| word)
                .chain(UNNAMED.iter().map(|&(word, _, _)| word))
                .collect();
            named.sort();
            let mut all = Reserved::ALL.to_vec();
            all.sort();
            assert_eq!(named, all);
        },
    );
    h.case(
        "tokens/the TypeScript-only tokens get the codes of SPEC 2",
        || {
            for &p in Punct::ALL {
                let expected = match p {
                    Punct::EqEqEq | Punct::BangEqEq => Some(enrang_diag::Code::EN0201),
                    Punct::Shr3 => Some(enrang_diag::Code::EN0208),
                    Punct::StarStar => Some(enrang_diag::Code::EN1022),
                    _ => None,
                };
                assert_eq!(p.habit_code(), expected, "{p:?}");
                if let Some(code) = expected {
                    let quoted = format!("`{}`", p.as_str());
                    assert!(code.title().contains(&quoted), "{code}: {}", code.title());
                }
            }
        },
    );
    h.case(
        "tokens/split_token splits what ARCHITECTURE 4 lists",
        || {
            let listed = listed_between(
                doc("ARCHITECTURE.md"),
                "`split_token` handles",
                "on the parser's request",
            );
            let split: Vec<String> = Punct::ALL
                .iter()
                .filter(|p| p.split().is_some())
                .map(|p| p.as_str().to_owned())
                .collect();
            let listed: BTreeSet<String> = listed.into_iter().collect();
            assert_eq!(split.into_iter().collect::<BTreeSet<_>>(), listed);
        },
    );
    let splits: &[(Punct, Punct, Punct)] = &[
        (Punct::Shr, Punct::Gt, Punct::Gt),
        (Punct::Shr3, Punct::Gt, Punct::Shr),
        (Punct::Ge, Punct::Gt, Punct::Eq),
        (Punct::ShrEq, Punct::Gt, Punct::Ge),
        (Punct::StarStar, Punct::Star, Punct::Star),
        (Punct::AmpAmp, Punct::Amp, Punct::Amp),
    ];
    for &(whole, first, second) in splits {
        h.case(format!("tokens/split {}", whole.as_str()), move || {
            assert_eq!(whole.split(), Some((first, second)));
            let spelled = format!("{}{}", first.as_str(), second.as_str());
            assert_eq!(spelled, whole.as_str());
            let len = whole.as_str().len() as u32;
            for space_before in [false, true] {
                let token = Token {
                    kind: TokenKind::Punct(whole),
                    span: Span {
                        lo: BytePos(10),
                        hi: BytePos(10 + len),
                    },
                    space_before,
                };
                let (head, tail) = token.split().expect("it splits");
                assert_eq!(head.kind, TokenKind::Punct(first));
                assert_eq!(tail.kind, TokenKind::Punct(second));
                assert_eq!((head.span.lo, head.span.hi), (BytePos(10), BytePos(11)));
                assert_eq!(
                    (tail.span.lo, tail.span.hi),
                    (BytePos(11), BytePos(10 + len))
                );
                assert_eq!(head.space_before, space_before);
                assert!(!tail.space_before);
            }
        });
    }
    h.case("tokens/nothing else splits", || {
        let splittable: BTreeSet<Punct> = splits.iter().map(|&(whole, _, _)| whole).collect();
        for &p in Punct::ALL {
            if !splittable.contains(&p) {
                assert_eq!(p.split(), None, "{p:?}");
            }
        }
        let ident = Token {
            kind: TokenKind::Keyword(Keyword::As),
            span: Span {
                lo: BytePos(1),
                hi: BytePos(3),
            },
            space_before: false,
        };
        assert_eq!(ident.split(), None);
    });
    h.case("tokens/the end-of-file token is empty at the end", || {
        let eof = Token::eof(BytePos(7), true);
        assert_eq!(eof.kind, TokenKind::Eof);
        assert!(eof.span.is_empty());
        assert_eq!(eof.span.lo, BytePos(7));
        assert!(eof.space_before);
        assert!(!eof.is(Punct::Semi));
        assert!(!eof.is_keyword(Keyword::If));
    });
}
