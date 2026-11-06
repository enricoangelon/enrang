//! `SourceMap`: line tables, columns, multi-file offsets, text extraction.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::sync::Arc;

use enrang_base::{BytePos, FileId, FileOrigin, Loc, SourceFile, SourceMap, Span};

const BOM: char = '\u{FEFF}';

fn add(map: &mut SourceMap, name: &str, text: &str) -> FileId {
    map.add(PathBuf::from(name), Arc::from(text), FileOrigin::User)
}

fn single(text: &str) -> (SourceMap, FileId) {
    let mut map = SourceMap::new();
    let id = add(&mut map, "test.en", text);
    (map, id)
}

fn at(map: &SourceMap, id: FileId, offset: u32) -> BytePos {
    map.file(id).start + offset
}

fn span(map: &SourceMap, id: FileId, lo: u32, hi: u32) -> Span {
    Span {
        lo: at(map, id, lo),
        hi: at(map, id, hi),
    }
}

fn line_col(map: &SourceMap, id: FileId, offset: u32) -> (u32, u32) {
    let loc = map.loc(at(map, id, offset));
    assert_eq!(loc.file, id);
    (loc.line, loc.col)
}

// ---------------------------------------------------------------- line starts

#[test]
fn line_starts_table() {
    let cases: &[(&str, &[u32])] = &[
        ("", &[0]),
        ("a", &[0]),
        ("abc", &[0]),
        ("\n", &[0, 1]),
        ("a\n", &[0, 2]),
        ("a\nb", &[0, 2]),
        ("a\nb\n", &[0, 2, 4]),
        ("\n\n", &[0, 1, 2]),
        ("\n\n\n", &[0, 1, 2, 3]),
        ("ab\ncd\nef", &[0, 3, 6]),
    ];
    for &(text, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.file(id).line_starts, expected, "{text:?}");
    }
}

#[test]
fn line_starts_with_crlf_table() {
    let cases: &[(&str, &[u32])] = &[
        ("\r\n", &[0, 2]),
        ("a\r\n", &[0, 3]),
        ("a\r\nb", &[0, 3]),
        ("\r\n\r\n", &[0, 2, 4]),
        ("a\r\nb\r\nc", &[0, 3, 6]),
        ("a\r\nb\nc", &[0, 3, 5]),
        ("a\nb\r\nc", &[0, 2, 5]),
        ("a\n\r\nb", &[0, 2, 4]),
    ];
    for &(text, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.file(id).line_starts, expected, "{text:?}");
    }
}

#[test]
fn only_lf_and_crlf_terminate_lines() {
    let cases: &[(&str, &[u32])] = &[
        ("\r", &[0]),
        ("a\r", &[0]),
        ("a\rb", &[0]),
        ("a\r\rb", &[0]),
        ("\r\r\n", &[0, 3]),
        ("\n\r", &[0, 1]),
        ("a\u{B}b", &[0]),
        ("a\u{C}b", &[0]),
        ("a\u{85}b", &[0]),
        ("a\u{2028}b", &[0]),
        ("a\u{2029}b", &[0]),
    ];
    for &(text, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.file(id).line_starts, expected, "{text:?}");
    }
}

#[test]
fn line_starts_are_byte_offsets_past_multibyte_text() {
    let cases: &[(&str, &[u32])] = &[
        ("é\nü", &[0, 3]),
        ("日本\n語", &[0, 7]),
        ("😀\n😀\n", &[0, 5, 10]),
        ("😀\r\n😀\n", &[0, 6, 11]),
    ];
    for &(text, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.file(id).line_starts, expected, "{text:?}");
    }
}

#[test]
fn line_starts_with_bom_table() {
    let cases: &[(&str, &[u32])] = &[
        ("\u{FEFF}", &[3]),
        ("\u{FEFF}a", &[3]),
        ("\u{FEFF}a\nb", &[3, 5]),
        ("\u{FEFF}\n", &[3, 4]),
        ("\u{FEFF}\u{FEFF}a", &[3]),
        ("a\u{FEFF}", &[0]),
        ("\n\u{FEFF}", &[0, 1]),
    ];
    for &(text, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.file(id).line_starts, expected, "{text:?}");
    }
}

#[test]
fn line_starts_are_relative_to_the_file() {
    let mut map = SourceMap::new();
    add(&mut map, "a.en", "long first file\nwith lines\n");
    let id = add(&mut map, "b.en", "x\ny");
    assert_eq!(map.file(id).line_starts, [0, 2]);
}

// ------------------------------------------------------------------ add, file

#[test]
fn add_assigns_sequential_ids() {
    let mut map = SourceMap::new();
    for expected in 0..5 {
        assert_eq!(add(&mut map, "f.en", "text"), FileId(expected));
    }
}

#[test]
fn file_returns_what_was_added() {
    let mut map = SourceMap::new();
    let text: Arc<str> = Arc::from("let x = 1;\n");
    add(&mut map, "first.en", "unrelated");
    let id = map.add(PathBuf::from("src/a.en"), text.clone(), FileOrigin::Library);
    let file: &SourceFile = map.file(id);
    assert_eq!(file.id, id);
    assert_eq!(file.path, Path::new("src/a.en"));
    assert_eq!(&*file.text, "let x = 1;\n");
    assert!(
        Arc::ptr_eq(&file.text, &text),
        "the text must not be copied"
    );
    assert_eq!(file.origin, FileOrigin::Library);
}

#[test]
fn origins_are_kept_table() {
    let outer = Span {
        lo: BytePos(3),
        hi: BytePos(9),
    };
    let origins = [
        FileOrigin::User,
        FileOrigin::Library,
        FileOrigin::Snippet { outer },
        FileOrigin::Snippet { outer: Span::DUMMY },
    ];
    let mut map = SourceMap::new();
    for origin in origins {
        let id = map.add(PathBuf::from("f.en"), Arc::from("x"), origin);
        assert_eq!(map.file(id).origin, origin);
    }
    assert_ne!(origins[0], origins[1]);
    assert_ne!(origins[2], origins[3]);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn file_panics_on_an_unknown_id() {
    let (map, _) = single("x");
    map.file(FileId(1));
}

#[test]
#[should_panic(expected = "out of bounds")]
fn file_panics_on_an_empty_map() {
    SourceMap::new().file(FileId(0));
}

#[test]
fn default_map_behaves_like_new() {
    let mut from_default = SourceMap::default();
    let mut from_new = SourceMap::new();
    let a = add(&mut from_default, "a.en", "xy");
    let b = add(&mut from_new, "a.en", "xy");
    assert_eq!((a, b), (FileId(0), FileId(0)));
    assert_eq!(from_default.file(a).start, from_new.file(b).start);
    assert_eq!(from_default.file(a).end(), from_new.file(b).end());
}

// ------------------------------------------------------- offsets across files

#[test]
fn first_file_starts_after_the_dummy_position() {
    let (map, id) = single("abc");
    assert_eq!(map.file(id).start, BytePos(1));
    assert_eq!(map.file(id).end(), BytePos(4));
    assert!(map.file(id).start > Span::DUMMY.hi);
}

#[test]
fn file_start_and_end_table() {
    // Each row is a list of file texts and their expected (start, end).
    type Row = (&'static [&'static str], &'static [(u32, u32)]);
    let cases: &[Row] = &[
        (&[""], &[(1, 1)]),
        (&["abc"], &[(1, 4)]),
        (&["abc", "de"], &[(1, 4), (5, 7)]),
        (&["", ""], &[(1, 1), (2, 2)]),
        (&["", "", ""], &[(1, 1), (2, 2), (3, 3)]),
        (&["abc", "", "", "de"], &[(1, 4), (5, 5), (6, 6), (7, 9)]),
        (&["é", "😀", "日"], &[(1, 3), (4, 8), (9, 12)]),
    ];
    for &(texts, expected) in cases {
        assert_eq!(texts.len(), expected.len());
        let mut map = SourceMap::new();
        for (text, &(start, end)) in texts.iter().zip(expected) {
            let id = add(&mut map, "f.en", text);
            assert_eq!(map.file(id).start, BytePos(start), "{texts:?}");
            assert_eq!(map.file(id).end(), BytePos(end), "{texts:?}");
        }
    }
}

#[test]
fn adding_a_file_does_not_move_earlier_files() {
    let mut map = SourceMap::new();
    let a = add(&mut map, "a.en", "abc\ndef");
    let before = map.loc(at(&map, a, 5));
    let start = map.file(a).start;
    add(&mut map, "b.en", "zzz");
    assert_eq!(map.file(a).start, start);
    assert_eq!(map.loc(at(&map, a, 5)), before);
}

fn boundary_map() -> (SourceMap, [FileId; 5]) {
    let mut map = SourceMap::new();
    let a = add(&mut map, "a.en", "abc"); // 1..=4
    let b = add(&mut map, "b.en", ""); // 5
    let c = add(&mut map, "c.en", ""); // 6
    let d = add(&mut map, "d.en", "xy\n"); // 7..=10
    let e = add(&mut map, "e.en", "é"); // 11..=13
    (map, [a, b, c, d, e])
}

#[test]
fn file_of_at_file_boundaries_table() {
    let (map, [a, b, c, d, e]) = boundary_map();
    let cases = [
        (1, a, "first byte of the first file"),
        (2, a, "inside a"),
        (3, a, "last byte of a"),
        (4, a, "end of file of a"),
        (5, b, "the only position of empty b"),
        (6, c, "the only position of empty c"),
        (7, d, "first byte of d"),
        (9, d, "newline of d"),
        (10, d, "end of file of d"),
        (11, e, "first byte of e"),
        (12, e, "inside a character of e"),
        (13, e, "end of file of the last file"),
    ];
    for (pos, expected, name) in cases {
        assert_eq!(map.file_of(BytePos(pos)).id, expected, "{name}");
    }
}

#[test]
fn file_of_covers_every_position_exactly_once() {
    let (map, ids) = boundary_map();
    let mut pos = 1;
    for id in ids {
        let file = map.file(id);
        assert_eq!(
            file.start,
            BytePos(pos),
            "no position between files is unowned"
        );
        while pos <= file.end().0 {
            assert_eq!(map.file_of(BytePos(pos)).id, id);
            pos += 1;
        }
    }
    assert_eq!(pos, 14);
}

#[test]
fn loc_across_several_files_table() {
    let mut map = SourceMap::new();
    let a = add(&mut map, "a.en", "ab\ncd");
    let b = add(&mut map, "b.en", "é\r\n😀x");
    let c = add(&mut map, "c.en", "");
    let d = add(&mut map, "d.en", "\n\nq");
    let cases = [
        (a, 0, 1, 1),
        (a, 2, 1, 3),
        (a, 3, 2, 1),
        (a, 5, 2, 3),
        (b, 0, 1, 1),
        (b, 2, 1, 2),
        (b, 4, 2, 1),
        (b, 8, 2, 2),
        (b, 9, 2, 3),
        (c, 0, 1, 1),
        (d, 0, 1, 1),
        (d, 1, 2, 1),
        (d, 2, 3, 1),
        (d, 3, 3, 2),
    ];
    for (file, offset, line, col) in cases {
        let expected = Loc { file, line, col };
        assert_eq!(
            map.loc(at(&map, file, offset)),
            expected,
            "{file:?} +{offset}"
        );
    }
}

#[test]
#[should_panic(expected = "position 0 is in no source file")]
fn file_of_panics_on_the_dummy_position() {
    let (map, _) = single("abc");
    map.file_of(Span::DUMMY.lo);
}

#[test]
#[should_panic(expected = "position 5 is in no source file")]
fn file_of_panics_just_past_the_last_file() {
    let (map, _) = single("abc");
    map.file_of(BytePos(5));
}

#[test]
#[should_panic(expected = "is in no source file")]
fn file_of_panics_far_past_the_last_file() {
    let (map, _) = single("abc");
    map.file_of(BytePos(u32::MAX));
}

#[test]
#[should_panic(expected = "position 1 is in no source file")]
fn file_of_panics_on_an_empty_map() {
    SourceMap::new().file_of(BytePos(1));
}

#[test]
#[should_panic(expected = "is in no source file")]
fn loc_panics_on_the_dummy_position() {
    let (map, _) = single("abc");
    map.loc(Span::DUMMY.lo);
}

// -------------------------------------------------------------------- columns

fn check_loc_table(cases: &[(&str, u32, u32, u32)]) {
    for &(text, offset, line, col) in cases {
        let (map, id) = single(text);
        assert_eq!(
            line_col(&map, id, offset),
            (line, col),
            "{text:?} at {offset}"
        );
    }
}

#[test]
fn loc_in_ascii_text() {
    check_loc_table(&[
        ("abc", 0, 1, 1),
        ("abc", 1, 1, 2),
        ("abc", 2, 1, 3),
        ("\tx", 1, 1, 2),
        ("\0x", 1, 1, 2),
        ("  x", 2, 1, 3),
    ]);
}

#[test]
fn loc_with_lf() {
    check_loc_table(&[
        ("a\nb", 1, 1, 2),
        ("a\nb", 2, 2, 1),
        ("a\nb", 3, 2, 2),
        ("\n", 0, 1, 1),
        ("\n\n", 1, 2, 1),
        ("ab\ncd\nef", 5, 2, 3),
        ("ab\ncd\nef", 6, 3, 1),
    ]);
}

#[test]
fn loc_with_crlf() {
    check_loc_table(&[
        ("a\r\nb", 1, 1, 2),
        ("a\r\nb", 2, 1, 3),
        ("a\r\nb", 3, 2, 1),
        ("a\r\nb", 4, 2, 2),
        ("\r\n\r\n", 2, 2, 1),
        ("\r\n\r\n", 3, 2, 2),
        ("a\r\nb\nc", 5, 3, 1),
    ]);
}

#[test]
fn loc_counts_a_bare_cr_as_a_column() {
    check_loc_table(&[("a\rb", 1, 1, 2), ("a\rb", 2, 1, 3), ("a\rb", 3, 1, 4)]);
}

#[test]
fn loc_at_end_of_file() {
    check_loc_table(&[
        ("abc", 3, 1, 4),
        ("a\n", 2, 2, 1),
        ("\n", 1, 2, 1),
        ("\n\n", 2, 3, 1),
        ("a\r\n", 3, 2, 1),
        ("ab\ncd", 5, 2, 3),
        ("é", 2, 1, 2),
        ("😀", 4, 1, 2),
        ("a\r", 2, 1, 3),
    ]);
}

#[test]
fn loc_in_an_empty_file() {
    check_loc_table(&[("", 0, 1, 1)]);
}

#[test]
fn columns_count_scalars_of_two_byte_characters() {
    check_loc_table(&[
        ("é", 0, 1, 1),
        ("éx", 2, 1, 2),
        ("éx", 3, 1, 3),
        ("aéb", 3, 1, 3),
        ("ééé", 4, 1, 3),
        ("é\nü", 3, 2, 1),
        ("é\nü", 5, 2, 2),
    ]);
}

#[test]
fn columns_count_scalars_of_three_byte_characters() {
    check_loc_table(&[
        ("日本語x", 3, 1, 2),
        ("日本語x", 6, 1, 3),
        ("日本語x", 9, 1, 4),
        ("日本語x", 10, 1, 5),
        ("a日b", 4, 1, 3),
    ]);
}

#[test]
fn columns_count_scalars_of_astral_characters() {
    check_loc_table(&[
        ("😀x", 4, 1, 2),
        ("😀x", 5, 1, 3),
        ("a😀b😀c", 5, 1, 3),
        ("a😀b😀c", 6, 1, 4),
        ("a😀b😀c", 10, 1, 5),
        ("a😀b😀c", 11, 1, 6),
        ("😀\r\n😀x", 4, 1, 2),
        ("😀\r\n😀x", 6, 2, 1),
        ("😀\r\n😀x", 10, 2, 2),
        ("😀\r\n😀x", 11, 2, 3),
        ("\u{10FFFF}x", 4, 1, 2),
    ]);
}

#[test]
fn columns_count_scalars_not_graphemes() {
    check_loc_table(&[
        ("e\u{301}x", 3, 1, 3),
        ("\u{1F1EE}\u{1F1F9}x", 8, 1, 3),
        ("\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}x", 18, 1, 6),
    ]);
}

#[test]
fn columns_at_every_utf8_length_boundary() {
    // U+7F, U+80, U+7FF, U+800, U+FFFF, U+10000 take 1, 2, 2, 3, 3 and 4 bytes.
    let text = "\u{7F}\u{80}\u{7FF}\u{800}\u{FFFF}\u{10000}x";
    let cases = [
        (0, 1),
        (1, 2),
        (3, 3),
        (5, 4),
        (8, 5),
        (11, 6),
        (15, 7),
        (16, 8),
    ];
    let (map, id) = single(text);
    for (offset, col) in cases {
        assert_eq!(line_col(&map, id, offset), (1, col), "offset {offset}");
    }
}

#[test]
fn position_inside_a_character_gets_that_characters_column() {
    check_loc_table(&[
        ("é", 1, 1, 1),
        ("😀x", 1, 1, 1),
        ("😀x", 2, 1, 1),
        ("😀x", 3, 1, 1),
        ("a日b", 2, 1, 2),
        ("a日b", 3, 1, 2),
        ("a\n日", 3, 2, 1),
        ("a\n日", 4, 2, 1),
    ]);
}

#[test]
fn a_leading_bom_is_not_a_column() {
    check_loc_table(&[
        ("\u{FEFF}abc", 0, 1, 1),
        ("\u{FEFF}abc", 1, 1, 1),
        ("\u{FEFF}abc", 2, 1, 1),
        ("\u{FEFF}abc", 3, 1, 1),
        ("\u{FEFF}abc", 4, 1, 2),
        ("\u{FEFF}abc", 6, 1, 4),
        ("\u{FEFF}", 0, 1, 1),
        ("\u{FEFF}", 3, 1, 1),
        ("\u{FEFF}a\nb", 4, 1, 2),
        ("\u{FEFF}a\nb", 5, 2, 1),
        ("\u{FEFF}a\nb", 6, 2, 2),
    ]);
}

#[test]
fn a_bom_elsewhere_is_an_ordinary_scalar() {
    check_loc_table(&[
        ("a\u{FEFF}b", 4, 1, 3),
        ("\n\u{FEFF}b", 4, 2, 2),
        ("\u{FEFF}\u{FEFF}x", 6, 1, 2),
    ]);
}

#[test]
fn loc_orders_by_file_then_line_then_col() {
    let loc = |file, line, col| Loc {
        file: FileId(file),
        line,
        col,
    };
    let mut locs = vec![loc(1, 1, 1), loc(0, 2, 1), loc(0, 1, 9), loc(0, 1, 2)];
    locs.sort();
    assert_eq!(
        locs,
        [loc(0, 1, 2), loc(0, 1, 9), loc(0, 2, 1), loc(1, 1, 1)]
    );
}

// ----------------------------------------------------------------------- text

#[test]
fn text_of_a_span_table() {
    let cases = [
        ("hello world", 0, 5, "hello"),
        ("hello world", 6, 11, "world"),
        ("hello world", 5, 6, " "),
        ("hello world", 0, 11, "hello world"),
        ("é日😀", 0, 2, "é"),
        ("é日😀", 2, 5, "日"),
        ("é日😀", 5, 9, "😀"),
        ("é日😀", 0, 9, "é日😀"),
        ("a\nb", 1, 2, "\n"),
        ("a\nb", 0, 3, "a\nb"),
        ("a\r\nb", 1, 3, "\r\n"),
        ("a\r\nb", 1, 2, "\r"),
        ("a\r\nb", 0, 4, "a\r\nb"),
        ("\u{FEFF}a", 3, 4, "a"),
        ("\u{FEFF}a", 0, 3, "\u{FEFF}"),
    ];
    for (text, lo, hi, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(
            map.text(span(&map, id, lo, hi)),
            expected,
            "{text:?} {lo}..{hi}"
        );
    }
}

#[test]
fn text_of_an_empty_span_table() {
    let cases = [
        ("abc", 0),
        ("abc", 1),
        ("abc", 3),
        ("", 0),
        ("é", 0),
        ("é", 2),
        ("\n", 1),
    ];
    for (text, offset) in cases {
        let (map, id) = single(text);
        assert_eq!(
            map.text(span(&map, id, offset, offset)),
            "",
            "{text:?} {offset}"
        );
    }
}

#[test]
fn text_of_dummy_is_empty() {
    let (map, _) = single("abc");
    assert_eq!(map.text(Span::DUMMY), "");
    assert_eq!(SourceMap::new().text(Span::DUMMY), "");
}

#[test]
fn text_uses_the_file_containing_the_span() {
    let mut map = SourceMap::new();
    let a = add(&mut map, "a.en", "first");
    let b = add(&mut map, "b.en", "");
    let c = add(&mut map, "c.en", "third");
    assert_eq!(map.text(span(&map, a, 1, 3)), "ir");
    assert_eq!(map.text(span(&map, b, 0, 0)), "");
    assert_eq!(map.text(span(&map, c, 1, 3)), "hi");
    assert_eq!(
        map.text(span(&map, a, 5, 5)),
        "",
        "end of file of the first file"
    );
    assert_eq!(map.text(span(&map, c, 0, 0)), "", "start of the third file");
}

#[test]
fn text_of_a_span_joined_with_to() {
    let (map, id) = single("let answer = 42;");
    let keyword = span(&map, id, 0, 3);
    let value = span(&map, id, 13, 15);
    assert_eq!(map.text(keyword.to(value)), "let answer = 42");
    assert_eq!(map.text(value.to(keyword)), "let answer = 42");
}

#[test]
#[should_panic(expected = "is inverted or leaves `b.en`")]
fn text_panics_on_a_span_crossing_into_the_next_file() {
    let mut map = SourceMap::new();
    add(&mut map, "a.en", "abc");
    let b = add(&mut map, "b.en", "de");
    add(&mut map, "c.en", "fgh");
    map.text(span(&map, b, 0, 3));
}

#[test]
#[should_panic(expected = "is inverted or leaves")]
fn text_panics_on_an_inverted_span() {
    let (map, id) = single("abcdef");
    map.text(span(&map, id, 4, 2));
}

#[test]
#[should_panic(expected = "is inverted or leaves")]
fn text_panics_on_an_inverted_span_ending_before_the_file() {
    let mut map = SourceMap::new();
    add(&mut map, "a.en", "abcdef");
    let b = add(&mut map, "b.en", "xyz");
    let lo = at(&map, b, 1);
    map.text(Span { lo, hi: BytePos(2) });
}

#[test]
#[should_panic(expected = "is inverted or leaves")]
fn text_panics_past_the_end_of_the_last_file() {
    let (map, id) = single("abc");
    map.text(span(&map, id, 1, 5));
}

#[test]
#[should_panic(expected = "char boundary")]
fn text_panics_when_a_span_splits_a_character() {
    let (map, id) = single("😀");
    map.text(span(&map, id, 0, 2));
}

#[test]
#[should_panic(expected = "is in no source file")]
fn text_panics_on_a_start_outside_every_file() {
    let (map, _) = single("abc");
    map.text(Span {
        lo: BytePos(9),
        hi: BytePos(9),
    });
}

#[test]
#[should_panic(expected = "is in no source file")]
fn text_panics_on_a_span_starting_at_the_dummy_position() {
    let (map, _) = single("abc");
    map.text(Span {
        lo: BytePos(0),
        hi: BytePos(2),
    });
}

// ------------------------------------------------------------------ line text

#[test]
fn line_text_table() {
    let cases = [
        ("", 1, ""),
        ("abc", 1, "abc"),
        ("abc\n", 1, "abc"),
        ("abc\n", 2, ""),
        ("a\nb\nc", 1, "a"),
        ("a\nb\nc", 2, "b"),
        ("a\nb\nc", 3, "c"),
        ("\n\n", 1, ""),
        ("\n\n", 2, ""),
        ("\n\n", 3, ""),
        ("  indented\t\n", 1, "  indented\t"),
        ("é日\n😀x\nz", 1, "é日"),
        ("é日\n😀x\nz", 2, "😀x"),
        ("é日\n😀x\nz", 3, "z"),
    ];
    for (text, line, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.line_text(id, line), expected, "{text:?} line {line}");
    }
}

#[test]
fn line_text_strips_crlf_table() {
    let cases = [
        ("a\r\nb\r\nc", 1, "a"),
        ("a\r\nb\r\nc", 2, "b"),
        ("a\r\nb\r\nc", 3, "c"),
        ("a\r\n", 1, "a"),
        ("a\r\n", 2, ""),
        ("\r\n\r\n", 1, ""),
        ("\r\n\r\n", 2, ""),
        ("\r\n\r\n", 3, ""),
        ("a\n\r\nb", 1, "a"),
        ("a\n\r\nb", 2, ""),
        ("a\n\r\nb", 3, "b"),
        ("😀\r\n", 1, "😀"),
    ];
    for (text, line, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.line_text(id, line), expected, "{text:?} line {line}");
    }
}

#[test]
fn line_text_keeps_a_cr_that_is_not_part_of_a_terminator() {
    let cases = [
        ("a\rb", 1, "a\rb"),
        ("a\r", 1, "a\r"),
        ("\r", 1, "\r"),
        ("\r\r\n", 1, "\r"),
        ("\r\r\n", 2, ""),
        ("a\r\rb\r\n", 1, "a\r\rb"),
        ("a\n\r", 2, "\r"),
    ];
    for (text, line, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.line_text(id, line), expected, "{text:?} line {line}");
    }
}

#[test]
fn line_text_omits_a_leading_bom_table() {
    let cases = [
        ("\u{FEFF}abc\nd", 1, "abc"),
        ("\u{FEFF}abc\nd", 2, "d"),
        ("\u{FEFF}", 1, ""),
        ("\u{FEFF}\n", 1, ""),
        ("\u{FEFF}\n", 2, ""),
        ("\u{FEFF}\u{FEFF}a", 1, "\u{FEFF}a"),
        ("a\n\u{FEFF}b", 2, "\u{FEFF}b"),
    ];
    for (text, line, expected) in cases {
        let (map, id) = single(text);
        assert_eq!(map.line_text(id, line), expected, "{text:?} line {line}");
    }
}

#[test]
fn line_text_columns_agree_with_loc() {
    // A renderer places carets by counting scalars of `line_text`, up to `col`.
    let text = "\u{FEFF}日本 x\r\n😀 y\nz";
    let (map, id) = single(text);
    for (needle, offset) in [('x', 10), ('y', 18), ('z', 20)] {
        let loc = map.loc(at(&map, id, offset));
        let line = map.line_text(id, loc.line);
        assert_eq!(line.chars().nth(loc.col as usize - 1), Some(needle));
    }
}

#[test]
fn line_text_is_per_file() {
    let mut map = SourceMap::new();
    let a = add(&mut map, "a.en", "a1\na2");
    let b = add(&mut map, "b.en", "");
    let c = add(&mut map, "c.en", "c1\r\nc2\r\n");
    assert_eq!(map.line_text(a, 2), "a2");
    assert_eq!(map.line_text(b, 1), "");
    assert_eq!(map.line_text(c, 1), "c1");
    assert_eq!(map.line_text(c, 2), "c2");
    assert_eq!(map.line_text(c, 3), "");
}

#[test]
#[should_panic(expected = "line 0 out of range: `test.en` has 1 lines")]
fn line_text_panics_on_line_zero() {
    let (map, id) = single("abc");
    map.line_text(id, 0);
}

#[test]
#[should_panic(expected = "line 2 out of range: `test.en` has 1 lines")]
fn line_text_panics_past_the_last_line() {
    let (map, id) = single("abc");
    map.line_text(id, 2);
}

#[test]
#[should_panic(expected = "line 3 out of range: `test.en` has 2 lines")]
fn line_text_panics_past_the_empty_line_after_a_final_newline() {
    let (map, id) = single("abc\n");
    map.line_text(id, 3);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn line_text_panics_on_an_unknown_file() {
    let (map, _) = single("abc");
    map.line_text(FileId(7), 1);
}

// --------------------------------------------------------- model-based checks

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn random_text(rng: &mut Rng) -> String {
    const PIECES: &[&str] = &[
        "a", "b", " ", "\t", "é", "日", "😀", "\n", "\n", "\r\n", "\r\n", "\r", "\u{301}",
        "\u{FEFF}", "\u{2028}",
    ];
    let mut text = String::new();
    if rng.below(4) == 0 {
        text.push(BOM);
    }
    for _ in 0..rng.below(40) {
        text.push_str(PIECES[rng.below(PIECES.len())]);
    }
    text
}

/// An independent oracle: walks the characters, tracking line and column.
fn walked_locs(text: &str) -> Vec<(u32, u32, u32)> {
    let mut locs = Vec::new();
    let (mut line, mut col) = (1, 1);
    for (i, c) in text.char_indices() {
        locs.push((i as u32, line, col));
        if i == 0 && c == BOM {
            continue;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    locs.push((text.len() as u32, line, col));
    locs
}

/// An independent oracle: `split` on LF, then drop the CR each LF ended.
fn split_lines(text: &str) -> Vec<&str> {
    let body = text.strip_prefix(BOM).unwrap_or(text);
    let pieces: Vec<&str> = body.split('\n').collect();
    let last = pieces.len() - 1;
    let lines = pieces.into_iter().enumerate();
    lines
        .map(|(i, p)| {
            if i < last {
                p.strip_suffix('\r').unwrap_or(p)
            } else {
                p
            }
        })
        .collect()
}

fn random_map(seed: u64, files: usize) -> (SourceMap, Vec<(FileId, String)>, Rng) {
    let mut rng = Rng(seed);
    let mut map = SourceMap::new();
    let mut added = Vec::new();
    for i in 0..files {
        let text = random_text(&mut rng);
        added.push((add(&mut map, &format!("f{i}.en"), &text), text));
    }
    (map, added, rng)
}

const SEEDS: [u64; 8] = [
    0x9E37_79B9_7F4A_7C15,
    1,
    2,
    0xDEAD_BEEF,
    42,
    0xFFFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
    0x0123_4567_89AB_CDEF,
];

#[test]
fn loc_matches_a_character_walk_on_random_files() {
    let mut checked = 0;
    for seed in SEEDS {
        let (map, added, _) = random_map(seed, 40);
        for (id, text) in &added {
            for (offset, line, col) in walked_locs(text) {
                assert_eq!(
                    line_col(&map, *id, offset),
                    (line, col),
                    "{text:?} at {offset}"
                );
                checked += 1;
            }
        }
    }
    assert!(
        checked > 5_000,
        "the generator produced too little: {checked}"
    );
}

#[test]
fn line_text_matches_a_split_on_random_files() {
    let mut checked = 0;
    for seed in SEEDS {
        let (map, added, _) = random_map(seed, 40);
        for (id, text) in &added {
            let lines = split_lines(text);
            assert_eq!(map.file(*id).line_starts.len(), lines.len(), "{text:?}");
            for (i, expected) in lines.iter().enumerate() {
                let line = i as u32 + 1;
                assert_eq!(map.line_text(*id, line), *expected, "{text:?} line {line}");
                checked += 1;
            }
        }
    }
    assert!(
        checked > 1_000,
        "the generator produced too little: {checked}"
    );
}

#[test]
fn text_matches_slicing_on_random_files() {
    let mut checked = 0;
    for seed in SEEDS {
        let (map, added, mut rng) = random_map(seed, 40);
        for (id, text) in &added {
            let boundaries: Vec<usize> = (0..=text.len())
                .filter(|&i| text.is_char_boundary(i))
                .collect();
            for _ in 0..20 {
                let a = boundaries[rng.below(boundaries.len())];
                let b = boundaries[rng.below(boundaries.len())];
                let (lo, hi) = (a.min(b), a.max(b));
                let got = map.text(span(&map, *id, lo as u32, hi as u32));
                assert_eq!(got, &text[lo..hi], "{text:?} {lo}..{hi}");
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 8 * 40 * 20);
}

#[test]
fn file_of_finds_the_owner_of_every_position_on_random_maps() {
    for seed in SEEDS {
        let (map, added, _) = random_map(seed, 60);
        let mut next = BytePos(1);
        for (id, text) in &added {
            let file = map.file(*id);
            assert_eq!(file.start, next);
            assert_eq!(file.end().0 - file.start.0, text.len() as u32);
            for pos in file.start.0..=file.end().0 {
                assert_eq!(map.file_of(BytePos(pos)).id, *id, "position {pos}");
            }
            next = file.end() + 1;
        }
    }
}

#[test]
fn identical_input_builds_identical_tables() {
    for seed in SEEDS {
        let (first, added, _) = random_map(seed, 10);
        let (second, _, _) = random_map(seed, 10);
        for (id, _) in &added {
            assert_eq!(first.file(*id).start, second.file(*id).start);
            assert_eq!(first.file(*id).line_starts, second.file(*id).line_starts);
        }
    }
}

#[test]
fn source_map_can_be_shared_between_threads() {
    let (map, id) = single("one\ntwo\n");
    let map = Arc::new(map);
    let handles: Vec<_> = (0..4)
        .map(|_| {
            let map = Arc::clone(&map);
            std::thread::spawn(move || map.line_text(id, 2).to_owned())
        })
        .collect();
    for handle in handles {
        assert_eq!(handle.join().unwrap(), "two");
    }
}
