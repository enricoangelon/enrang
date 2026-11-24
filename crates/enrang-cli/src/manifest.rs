//! `enrang.json` (ARCHITECTURE 11): `{"name":"hello","entry":"src/main.en",
//! "target":"x86_64-linux"}`, optionally `cpu`, `float` and `base`.
//!
//! It is read from the working directory. Its `entry` is the file a command takes
//! when it is given none, and `target`, `cpu` and `float` are defaults that the
//! flags of the same names override. A malformed file is a usage message: SPEC 13.2
//! has no code for it.

use std::fs;
use std::io;
use std::path::Path;

use enrang_diag::{did_you_mean, shown};

use crate::flags::listed;
use crate::outcome::Outcome;
use crate::report::{complaint, noted_complaint};

/// The file's name.
pub(crate) const FILE: &str = "enrang.json";

/// Its keys, in the order ARCHITECTURE 11 names them.
const KEYS: &[&str] = &["name", "entry", "target", "cpu", "float", "base"];

/// How deep arrays and objects may nest before the file is refused, so that no
/// file can exhaust the stack.
const MAX_DEPTH: usize = 64;

/// What a command reads from the file. `name` is for `build`, and `base` for the
/// flat and image outputs of `build`, so no command reads them yet; their types are
/// still checked.
#[derive(Clone, Default, Eq, PartialEq, Debug)]
pub(crate) struct Manifest {
    pub entry: Option<String>,
    pub target: Option<String>,
    pub cpu: Option<String>,
    pub float: Option<String>,
}

/// The manifest in `dir`, or `None` when there is no such file.
pub(crate) fn read(dir: &Path) -> Result<Option<Manifest>, Outcome> {
    let bytes = match fs::read(dir.join(FILE)) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(complaint(
                &format!("cannot read {FILE}: {}", error.kind()),
                None,
                None,
            ));
        }
    };
    let invalid = |text: &str, at: usize| {
        let (line, column) = line_and_column(text, at);
        complaint(
            &format!("{FILE} is not valid JSON: line {line}, column {column}"),
            None,
            None,
        )
    };
    let text = match std::str::from_utf8(&bytes) {
        Ok(text) => text,
        Err(error) => {
            let valid = std::str::from_utf8(&bytes[..error.valid_up_to()]).unwrap_or_default();
            return Err(invalid(valid, valid.len()));
        }
    };
    let value = parse(text).map_err(|at| invalid(text, at))?;
    let Value::Object(fields) = value else {
        return Err(complaint(
            &format!("{FILE} must hold one object"),
            None,
            None,
        ));
    };
    let mut manifest = Manifest::default();
    for (key, value) in fields {
        if !KEYS.contains(&key.as_str()) {
            return Err(unknown_key(&key));
        }
        let text = match value {
            Value::Str(text) => text,
            Value::Number if key == "base" => continue,
            _ if key == "base" => return Err(wrong_type(&key, "a string or a number")),
            _ => return Err(wrong_type(&key, "a string")),
        };
        match key.as_str() {
            "entry" => manifest.entry = Some(text),
            "target" => manifest.target = Some(text),
            "cpu" => manifest.cpu = Some(text),
            "float" => manifest.float = Some(text),
            _ => {}
        }
    }
    Ok(Some(manifest))
}

fn wrong_type(key: &str, wanted: &str) -> Outcome {
    complaint(
        &format!("`{}` in {FILE} must be {wanted}", shown(key)),
        None,
        None,
    )
}

fn unknown_key(key: &str) -> Outcome {
    let help = did_you_mean(key, KEYS).map(|close| format!("did you mean `{close}`?"));
    noted_complaint(
        &format!("`{}` in {FILE} is not one of its keys", shown(key)),
        help.as_deref(),
        Some(&format!("the keys of {FILE} are {}", listed(KEYS))),
        None,
    )
}

/// The line and column of a byte offset, both from 1, columns in characters.
fn line_and_column(text: &str, at: usize) -> (usize, usize) {
    let before = &text[..at.min(text.len())];
    let line = before.matches('\n').count() + 1;
    let start = before.rfind('\n').map_or(0, |newline| newline + 1);
    (line, before[start..].chars().count() + 1)
}

/// A JSON value, with only what the manifest needs of each kind.
#[derive(Clone, Debug)]
enum Value {
    Str(String),
    Number,
    /// `true`, `false`, `null` or an array.
    Other,
    Object(Vec<(String, Value)>),
}

/// Parses a whole document (RFC 8259); `Err` is the byte offset of the first
/// character that does not fit.
fn parse(text: &str) -> Result<Value, usize> {
    let mut parser = Parser {
        bytes: text.as_bytes(),
        at: 0,
    };
    let value = parser.value(0)?;
    parser.space();
    if parser.at < parser.bytes.len() {
        return Err(parser.at);
    }
    Ok(value)
}

struct Parser<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.at).copied()
    }

    fn space(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.at += 1;
        }
    }

    fn eat(&mut self, byte: u8) -> Result<(), usize> {
        if self.peek() == Some(byte) {
            self.at += 1;
            Ok(())
        } else {
            Err(self.at)
        }
    }

    fn value(&mut self, depth: usize) -> Result<Value, usize> {
        self.space();
        if depth > MAX_DEPTH {
            return Err(self.at);
        }
        match self.peek() {
            Some(b'{') => self.object(depth),
            Some(b'[') => self.array(depth),
            Some(b'"') => self.string().map(Value::Str),
            Some(b'-' | b'0'..=b'9') => self.number(),
            _ => {
                for word in ["true", "false", "null"] {
                    if self.bytes[self.at..].starts_with(word.as_bytes()) {
                        self.at += word.len();
                        return Ok(Value::Other);
                    }
                }
                Err(self.at)
            }
        }
    }

    fn object(&mut self, depth: usize) -> Result<Value, usize> {
        self.eat(b'{')?;
        let mut fields = Vec::new();
        self.space();
        if self.peek() == Some(b'}') {
            self.at += 1;
            return Ok(Value::Object(fields));
        }
        loop {
            self.space();
            if self.peek() != Some(b'"') {
                return Err(self.at);
            }
            let key = self.string()?;
            self.space();
            self.eat(b':')?;
            let value = self.value(depth + 1)?;
            fields.push((key, value));
            self.space();
            match self.peek() {
                Some(b',') => self.at += 1,
                Some(b'}') => {
                    self.at += 1;
                    return Ok(Value::Object(fields));
                }
                _ => return Err(self.at),
            }
        }
    }

    fn array(&mut self, depth: usize) -> Result<Value, usize> {
        self.eat(b'[')?;
        self.space();
        if self.peek() == Some(b']') {
            self.at += 1;
            return Ok(Value::Other);
        }
        loop {
            self.value(depth + 1)?;
            self.space();
            match self.peek() {
                Some(b',') => self.at += 1,
                Some(b']') => {
                    self.at += 1;
                    return Ok(Value::Other);
                }
                _ => return Err(self.at),
            }
        }
    }

    fn digits(&mut self) -> usize {
        let start = self.at;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.at += 1;
        }
        self.at - start
    }

    fn number(&mut self) -> Result<Value, usize> {
        if self.peek() == Some(b'-') {
            self.at += 1;
        }
        match self.peek() {
            Some(b'0') => self.at += 1,
            Some(b'1'..=b'9') => {
                self.digits();
            }
            _ => return Err(self.at),
        }
        if self.peek() == Some(b'.') {
            self.at += 1;
            if self.digits() == 0 {
                return Err(self.at);
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.at += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.at += 1;
            }
            if self.digits() == 0 {
                return Err(self.at);
            }
        }
        Ok(Value::Number)
    }

    fn hex4(&mut self) -> Result<u32, usize> {
        let digits = self.bytes.get(self.at..self.at + 4).ok_or(self.at)?;
        let text = std::str::from_utf8(digits).map_err(|_| self.at)?;
        if !text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(self.at);
        }
        let value = u32::from_str_radix(text, 16).map_err(|_| self.at)?;
        self.at += 4;
        Ok(value)
    }

    fn string(&mut self) -> Result<String, usize> {
        self.eat(b'"')?;
        let mut text = String::new();
        loop {
            let start = self.at;
            while let Some(byte) = self.peek() {
                if byte == b'"' || byte == b'\\' || byte < 0x20 {
                    break;
                }
                self.at += 1;
            }
            // The input is a `str`, and the run stops only at ASCII bytes, so it
            // ends on a character boundary.
            text.push_str(std::str::from_utf8(&self.bytes[start..self.at]).map_err(|_| start)?);
            match self.peek() {
                Some(b'"') => {
                    self.at += 1;
                    return Ok(text);
                }
                Some(b'\\') => {
                    let escape = self.at;
                    self.at += 1;
                    let byte = self.peek().ok_or(self.at)?;
                    self.at += 1;
                    let decoded = match byte {
                        b'"' => '"',
                        b'\\' => '\\',
                        b'/' => '/',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'u' => self.unicode_escape(escape)?,
                        _ => return Err(escape),
                    };
                    text.push(decoded);
                }
                _ => return Err(self.at),
            }
        }
    }

    /// The rest of a `\u` escape, a surrogate pair included.
    fn unicode_escape(&mut self, escape: usize) -> Result<char, usize> {
        let first = self.hex4()?;
        let scalar = match first {
            0xD800..=0xDBFF => {
                if !self.bytes[self.at..].starts_with(b"\\u") {
                    return Err(escape);
                }
                self.at += 2;
                let second = self.hex4()?;
                if !(0xDC00..=0xDFFF).contains(&second) {
                    return Err(escape);
                }
                0x10000 + ((first - 0xD800) << 10) + (second - 0xDC00)
            }
            0xDC00..=0xDFFF => return Err(escape),
            _ => first,
        };
        char::from_u32(scalar).ok_or(escape)
    }
}

#[cfg(test)]
mod tests {
    use super::{Value, line_and_column, parse};

    fn fields(text: &str) -> Vec<String> {
        match parse(text) {
            Ok(Value::Object(fields)) => fields.into_iter().map(|(key, _)| key).collect(),
            other => panic!("{text}: {other:?}"),
        }
    }

    #[test]
    fn documents_that_parse() {
        assert_eq!(fields("{}"), Vec::<String>::new());
        assert_eq!(
            fields(" { \"a\" : 1 , \"b\":[true,null,{\"c\":-0.5e+3}] } "),
            ["a", "b"]
        );
        assert_eq!(
            fields("{\"\\u00e9\\ud83d\\ude00\\n\":\"\"}"),
            ["\u{e9}\u{1f600}\n"]
        );
        assert!(matches!(parse("[1, 2]"), Ok(Value::Other)));
        assert!(matches!(parse("\"x\""), Ok(Value::Str(text)) if text == "x"));
    }

    #[test]
    fn documents_that_do_not_parse_and_where() {
        let rows: &[(&str, usize)] = &[
            ("", 0),
            ("{", 1),
            ("{\"a\" 1}", 5),
            ("{\"a\":1,}", 7),
            ("{\"a\":01}", 6),
            ("{\"a\":1.}", 7),
            ("{\"a\":\"\\x\"}", 6),
            ("{\"a\":\"\\ud800\"}", 6),
            ("{\"a\":\"\\udc00\"}", 6),
            ("{\"a\":\"\n\"}", 6),
            ("{} x", 3),
            ("tru", 0),
            ("{a:1}", 1),
        ];
        for (text, at) in rows {
            assert_eq!(parse(text).err(), Some(*at), "{text:?}");
        }
    }

    #[test]
    fn deep_nesting_is_refused_not_a_crash() {
        let deep = "[".repeat(100_000);
        assert!(parse(&deep).is_err());
    }

    #[test]
    fn positions_count_lines_and_characters() {
        assert_eq!(line_and_column("ab", 1), (1, 2));
        assert_eq!(line_and_column("a\néb", 4), (2, 2));
        assert_eq!(line_and_column("a\n", 2), (2, 1));
    }
}
