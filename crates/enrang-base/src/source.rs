//! Spans and the source map (ARCHITECTURE 2.1).
//!
//! Positions are global: every file of a session occupies its own range of
//! `BytePos` values. Position 0 belongs to no file, so `Span::DUMMY` can never
//! be mistaken for real source. One position separates consecutive files, so
//! the end-of-file position of each file, empty files included, is unambiguous.

use std::ops::Add;
use std::path::PathBuf;
use std::sync::Arc;

use crate::index::{IdVec, Idx};

/// The byte order mark. SPEC 2 skips it when it leads a file.
const BOM: &str = "\u{FEFF}";

/// A global byte offset across all files of a session.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct BytePos(pub u32);

impl Add<u32> for BytePos {
    type Output = BytePos;

    fn add(self, offset: u32) -> BytePos {
        BytePos(self.0 + offset)
    }
}

/// A half-open byte range `lo..hi`. Spans order by `lo`, then `hi`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Span {
    pub lo: BytePos,
    pub hi: BytePos,
}

impl Span {
    /// The span of things that have no source. No file contains it.
    pub const DUMMY: Span = Span {
        lo: BytePos(0),
        hi: BytePos(0),
    };

    /// The smallest span enclosing both spans, whichever comes first. A dummy
    /// span has no location, so it contributes nothing.
    pub fn to(self, end: Span) -> Span {
        if self.is_dummy() {
            return end;
        }
        if end.is_dummy() {
            return self;
        }
        Span {
            lo: self.lo.min(end.lo),
            hi: self.hi.max(end.hi),
        }
    }

    pub fn is_dummy(self) -> bool {
        self == Span::DUMMY
    }

    /// True for a zero-width span, which `DUMMY` also is.
    pub fn is_empty(self) -> bool {
        self.lo == self.hi
    }
}

/// Identifies a file of a `SourceMap`, in the order files were added.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct FileId(pub u32);

impl Idx for FileId {
    fn new(i: usize) -> Self {
        FileId(u32::try_from(i).expect("file index exceeds u32"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// Where a file's text came from.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum FileOrigin {
    User,
    Library,
    /// A `compileFails` snippet; `outer` is its place in the enclosing file.
    Snippet {
        outer: Span,
    },
}

#[derive(Clone, Debug)]
pub struct SourceFile {
    pub id: FileId,
    pub path: PathBuf,
    pub text: Arc<str>,
    pub start: BytePos,
    /// File-relative byte offset where each line begins. Never empty. A leading
    /// BOM is outside line 1, which then begins at offset 3.
    pub line_starts: Vec<u32>,
    pub origin: FileOrigin,
}

impl SourceFile {
    /// The end-of-file position: one past the last byte.
    pub fn end(&self) -> BytePos {
        self.start + self.text.len() as u32
    }
}

/// A line and column for rendering. Both count from 1, and columns count
/// Unicode scalar values (SPEC 2).
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Loc {
    pub file: FileId,
    pub line: u32,
    pub col: u32,
}

/// All source files of a session. Files are never removed, so their ids are
/// also their order by `start`.
#[derive(Debug, Default)]
pub struct SourceMap {
    files: IdVec<FileId, SourceFile>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a file after the existing ones. Panics if the session's total text
    /// no longer fits in `BytePos`.
    pub fn add(&mut self, path: PathBuf, text: Arc<str>, origin: FileOrigin) -> FileId {
        let prev_end = self.files.as_slice().last().map(SourceFile::end);
        let start = place_after(prev_end, text.len()).expect("source text exceeds BytePos range");
        let line_starts = line_starts(&text);
        let id = self.files.next_index();
        self.files.push(SourceFile {
            id,
            path,
            text,
            start,
            line_starts,
            origin,
        })
    }

    /// Panics if `id` is not from this map.
    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id]
    }

    /// The file containing `pos`, counting its end-of-file position. Panics if
    /// there is none, as for `DUMMY`'s position.
    pub fn file_of(&self, pos: BytePos) -> &SourceFile {
        let files = self.files.as_slice();
        let after = files.partition_point(|file| file.start <= pos);
        match after.checked_sub(1).map(|i| &files[i]) {
            Some(file) if pos <= file.end() => file,
            _ => panic!("position {} is in no source file", pos.0),
        }
    }

    /// The line and column of `pos`. A position inside a multi-byte character
    /// gets that character's column; one inside a leading BOM gets line 1,
    /// column 1. Panics as `file_of` does.
    pub fn loc(&self, pos: BytePos) -> Loc {
        let file = self.file_of(pos);
        let offset = pos.0 - file.start.0;
        let line = file.line_starts.partition_point(|&s| s <= offset).max(1);
        let line_start = file.line_starts[line - 1] as usize;
        let end = file.text.floor_char_boundary(offset as usize);
        let col = match file.text.get(line_start..end) {
            Some(before) => before.chars().count() as u32 + 1,
            None => 1,
        };
        Loc {
            file: file.id,
            line: line as u32,
            col,
        }
    }

    /// The source text of `span`, or `""` for `DUMMY`. Panics if the span is
    /// inverted, leaves its file or splits a character.
    pub fn text(&self, span: Span) -> &str {
        if span.is_dummy() {
            return "";
        }
        let file = self.file_of(span.lo);
        assert!(
            span.lo <= span.hi && span.hi <= file.end(),
            "span {}..{} is inverted or leaves `{}`",
            span.lo.0,
            span.hi.0,
            file.path.display(),
        );
        let lo = span.lo.0 - file.start.0;
        let hi = span.hi.0 - file.start.0;
        &file.text[lo as usize..hi as usize]
    }

    /// The text of 1-based `line`, without its LF or CRLF terminator and without
    /// a leading BOM. Panics if the file has no such line.
    pub fn line_text(&self, file: FileId, line: u32) -> &str {
        let file = self.file(file);
        let starts = &file.line_starts;
        let Some(index) = (line as usize).checked_sub(1).filter(|&i| i < starts.len()) else {
            panic!(
                "line {line} out of range: `{}` has {} lines",
                file.path.display(),
                starts.len(),
            );
        };
        let start = starts[index] as usize;
        match starts.get(index + 1) {
            // Only the last line can lack a terminator, so a bare CR ending it stays.
            None => &file.text[start..],
            Some(&next) => {
                let with_cr = &file.text[start..next as usize - 1];
                with_cr.strip_suffix('\r').unwrap_or(with_cr)
            }
        }
    }
}

/// Where a file of `len` bytes starts when placed after a file ending at
/// `prev_end`, or `None` if its end would not fit in `BytePos`.
fn place_after(prev_end: Option<BytePos>, len: usize) -> Option<BytePos> {
    let start = match prev_end {
        Some(end) => end.0.checked_add(1)?,
        None => 1,
    };
    start.checked_add(u32::try_from(len).ok()?)?;
    Some(BytePos(start))
}

/// LF ends a line and CRLF ends with LF, so only LF needs finding. A bare CR
/// is not a terminator (SPEC 2).
fn line_starts(text: &str) -> Vec<u32> {
    let first = if text.starts_with(BOM) { BOM.len() } else { 0 };
    let mut starts = vec![first as u32];
    let newlines = text.bytes().enumerate().filter(|&(_, b)| b == b'\n');
    starts.extend(newlines.map(|(i, _)| i as u32 + 1));
    starts
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX: u32 = u32::MAX;

    #[test]
    fn place_after_table() {
        let cases = [
            (None, 0, Some(1)),
            (None, 5, Some(1)),
            (Some(4), 0, Some(5)),
            (Some(4), 7, Some(5)),
            (None, MAX as usize - 1, Some(1)),
            (None, MAX as usize, None),
            (None, MAX as usize + 1, None),
            (Some(MAX - 1), 0, Some(MAX)),
            (Some(MAX - 1), 1, None),
            (Some(MAX), 0, None),
            (Some(10), MAX as usize - 11, Some(11)),
            (Some(10), MAX as usize - 10, None),
        ];
        for (prev_end, len, expected) in cases {
            let got = place_after(prev_end.map(BytePos), len);
            assert_eq!(got, expected.map(BytePos), "{prev_end:?} {len}");
        }
    }

    fn map_ending_at(end: u32) -> SourceMap {
        let mut map = SourceMap::new();
        map.files.push(SourceFile {
            id: FileId(0),
            path: PathBuf::from("full.en"),
            text: Arc::from(""),
            start: BytePos(end),
            line_starts: vec![0],
            origin: FileOrigin::User,
        });
        map
    }

    #[test]
    fn add_accepts_a_file_ending_at_the_last_position() {
        let mut map = map_ending_at(MAX - 2);
        let id = map.add(PathBuf::from("b.en"), Arc::from("x"), FileOrigin::User);
        assert_eq!(map.file(id).start, BytePos(MAX - 1));
        assert_eq!(map.file(id).end(), BytePos(MAX));
        assert_eq!(map.file_of(BytePos(MAX)).id, id);
    }

    #[test]
    #[should_panic(expected = "source text exceeds BytePos range")]
    fn add_panics_when_text_does_not_fit() {
        let mut map = map_ending_at(MAX - 2);
        map.add(PathBuf::from("b.en"), Arc::from("xy"), FileOrigin::User);
    }

    #[test]
    #[should_panic(expected = "source text exceeds BytePos range")]
    fn add_panics_when_no_position_is_left() {
        let mut map = map_ending_at(MAX);
        map.add(PathBuf::from("b.en"), Arc::from(""), FileOrigin::User);
    }
}
