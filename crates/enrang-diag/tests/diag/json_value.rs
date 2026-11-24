//! A small strict JSON reader, so that the suite can check `render_json` as a
//! consumer would and not by pattern-matching text.

#[derive(Clone, PartialEq, Debug)]
pub enum J {
    Null,
    Bool(bool),
    Int(i64),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

impl J {
    #[track_caller]
    pub fn get(&self, key: &str) -> &J {
        let J::Obj(fields) = self else {
            panic!("not an object: {self:?}");
        };
        &fields
            .iter()
            .find(|(name, _)| name == key)
            .unwrap_or_else(|| panic!("no field `{key}` in {self:?}"))
            .1
    }

    /// The field names, in order.
    #[track_caller]
    pub fn keys(&self) -> Vec<&str> {
        let J::Obj(fields) = self else {
            panic!("not an object: {self:?}");
        };
        fields.iter().map(|(name, _)| name.as_str()).collect()
    }

    #[track_caller]
    pub fn str(&self) -> &str {
        match self {
            J::Str(text) => text,
            other => panic!("not a string: {other:?}"),
        }
    }

    #[track_caller]
    pub fn int(&self) -> i64 {
        match self {
            J::Int(value) => *value,
            other => panic!("not an integer: {other:?}"),
        }
    }

    #[track_caller]
    pub fn arr(&self) -> &[J] {
        match self {
            J::Arr(items) => items,
            other => panic!("not an array: {other:?}"),
        }
    }
}

pub fn parse(text: &str) -> Result<J, String> {
    let chars: Vec<char> = text.chars().collect();
    let mut reader = Reader { chars, at: 0 };
    let value = reader.value()?;
    if reader.at != reader.chars.len() {
        return Err(format!("text after the value at {}", reader.at));
    }
    Ok(value)
}

struct Reader {
    chars: Vec<char>,
    at: usize,
}

impl Reader {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.at).copied()
    }

    fn expect(&mut self, c: char) -> Result<(), String> {
        if self.peek() == Some(c) {
            self.at += 1;
            Ok(())
        } else {
            Err(format!(
                "wanted {c:?} at {}, got {:?}",
                self.at,
                self.peek()
            ))
        }
    }

    fn keyword(&mut self, word: &str, value: J) -> Result<J, String> {
        for c in word.chars() {
            self.expect(c)?;
        }
        Ok(value)
    }

    fn value(&mut self) -> Result<J, String> {
        match self.peek() {
            Some('n') => self.keyword("null", J::Null),
            Some('t') => self.keyword("true", J::Bool(true)),
            Some('f') => self.keyword("false", J::Bool(false)),
            Some('"') => self.string().map(J::Str),
            Some('[') => self.array(),
            Some('{') => self.object(),
            Some(c) if c == '-' || c.is_ascii_digit() => self.integer(),
            other => Err(format!("no value at {}: {other:?}", self.at)),
        }
    }

    fn integer(&mut self) -> Result<J, String> {
        let start = self.at;
        if self.peek() == Some('-') {
            self.at += 1;
        }
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.at += 1;
        }
        let text: String = self.chars[start..self.at].iter().collect();
        text.parse()
            .map(J::Int)
            .map_err(|_| format!("bad number `{text}`"))
    }

    fn string(&mut self) -> Result<String, String> {
        self.expect('"')?;
        let mut out = String::new();
        loop {
            let c = self.peek().ok_or("an unterminated string")?;
            self.at += 1;
            match c {
                '"' => return Ok(out),
                '\\' => out.push(self.escape()?),
                c if (c as u32) < 0x20 => return Err(format!("raw control {c:?} in a string")),
                c => out.push(c),
            }
        }
    }

    fn escape(&mut self) -> Result<char, String> {
        let c = self.peek().ok_or("an unterminated escape")?;
        self.at += 1;
        Ok(match c {
            '"' => '"',
            '\\' => '\\',
            '/' => '/',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            'b' => '\u{8}',
            'f' => '\u{c}',
            'u' => {
                let hex: String = self
                    .chars
                    .get(self.at..self.at + 4)
                    .ok_or("a short \\u escape")?
                    .iter()
                    .collect();
                self.at += 4;
                let code = u32::from_str_radix(&hex, 16).map_err(|_| "bad \\u escape")?;
                char::from_u32(code).ok_or("a \\u escape that is no scalar")?
            }
            other => return Err(format!("unknown escape \\{other}")),
        })
    }

    fn array(&mut self) -> Result<J, String> {
        self.expect('[')?;
        let mut items = Vec::new();
        if self.peek() == Some(']') {
            self.at += 1;
            return Ok(J::Arr(items));
        }
        loop {
            items.push(self.value()?);
            match self.peek() {
                Some(',') => self.at += 1,
                Some(']') => {
                    self.at += 1;
                    return Ok(J::Arr(items));
                }
                other => return Err(format!("bad array at {}: {other:?}", self.at)),
            }
        }
    }

    fn object(&mut self) -> Result<J, String> {
        self.expect('{')?;
        let mut fields: Vec<(String, J)> = Vec::new();
        if self.peek() == Some('}') {
            self.at += 1;
            return Ok(J::Obj(fields));
        }
        loop {
            let key = self.string()?;
            if fields.iter().any(|(name, _)| *name == key) {
                return Err(format!("field `{key}` is repeated"));
            }
            self.expect(':')?;
            fields.push((key, self.value()?));
            match self.peek() {
                Some(',') => self.at += 1,
                Some('}') => {
                    self.at += 1;
                    return Ok(J::Obj(fields));
                }
                other => return Err(format!("bad object at {}: {other:?}", self.at)),
            }
        }
    }
}

/// The reader itself has to reject what a sloppy writer would produce.
pub fn register(h: &mut enrang_testkit::Harness) {
    let rejected = [
        "",
        "{",
        "}",
        "[1,]",
        "{\"a\":1,}",
        "{\"a\":1,\"a\":2}",
        "\"a",
        "\"\n\"",
        "\"\\q\"",
        "\"\\u12\"",
        "nul",
        "1 2",
        "{a:1}",
    ];
    for text in rejected {
        h.case(format!("json reader/rejects {text:?}"), move || {
            assert!(parse(text).is_err(), "{text:?} parsed");
        });
    }
    let accepted: [(&str, J); 7] = [
        ("null", J::Null),
        ("true", J::Bool(true)),
        ("-12", J::Int(-12)),
        ("\"a\\n\\u0041\"", J::Str("a\nA".to_owned())),
        ("[]", J::Arr(Vec::new())),
        ("[1,[2]]", J::Arr(vec![J::Int(1), J::Arr(vec![J::Int(2)])])),
        ("{\"k\":null}", J::Obj(vec![("k".to_owned(), J::Null)])),
    ];
    for (text, value) in accepted {
        h.case(format!("json reader/accepts {text}"), move || {
            assert_eq!(parse(text), Ok(value));
        });
    }
}
