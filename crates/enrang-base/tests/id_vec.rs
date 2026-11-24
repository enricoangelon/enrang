//! `Idx` and `IdVec`.

#![forbid(unsafe_code)]

use enrang_base::{FileId, IdVec, Idx};

/// Deliberately implements only what `Idx` demands: every `IdVec` trait impl
/// must work without `Debug`, `Hash` or `Default` on the index.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
struct Bare(u32);

impl Idx for Bare {
    fn new(i: usize) -> Self {
        Bare(i as u32)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct Ix(u32);

impl Idx for Ix {
    fn new(i: usize) -> Self {
        Ix(u32::try_from(i).expect("index fits u32"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

type V<T> = IdVec<Ix, T>;

#[test]
fn new_is_empty() {
    let v: V<char> = IdVec::new();
    assert_eq!(v.len(), 0);
    assert!(v.is_empty());
    assert_eq!(v.next_index(), Ix(0));
    assert_eq!(v.get(Ix(0)), None);
    assert_eq!(v.iter().count(), 0);
    assert_eq!(v.indices().count(), 0);
}

#[test]
fn default_is_empty_even_without_a_default_payload() {
    struct NoDefault;
    let mut v: V<NoDefault> = IdVec::default();
    assert!(v.is_empty());
    assert_eq!(v.push(NoDefault), Ix(0));
}

#[test]
fn with_capacity_has_no_elements() {
    let mut v: V<u8> = IdVec::with_capacity(16);
    assert!(v.is_empty());
    assert_eq!(v.push(9), Ix(0));
    assert_eq!(v.len(), 1);
}

#[test]
fn push_returns_sequential_indices() {
    let mut v = V::new();
    for i in 0..10 {
        assert_eq!(v.next_index(), Ix(i));
        assert_eq!(v.push(i * 3), Ix(i));
        assert_eq!(v.len(), i as usize + 1);
        assert!(!v.is_empty());
    }
}

#[test]
fn growth_keeps_every_element_table() {
    for size in [
        1u32, 2, 3, 4, 5, 7, 8, 9, 63, 64, 65, 1023, 1024, 1025, 20_000,
    ] {
        let mut v: V<u32> = IdVec::new();
        let ids: Vec<Ix> = (0..size).map(|i| v.push(i ^ 0x5A5A)).collect();
        assert_eq!(v.len(), size as usize);
        for (i, id) in ids.into_iter().enumerate() {
            assert_eq!(id, Ix(i as u32));
            assert_eq!(v[id], i as u32 ^ 0x5A5A);
        }
    }
}

#[test]
fn index_reads_and_index_mut_writes() {
    let mut v: V<String> = IdVec::new();
    let a = v.push("a".to_owned());
    let b = v.push("b".to_owned());
    assert_eq!(v[a], "a");
    assert_eq!(v[b], "b");
    v[a].push('!');
    assert_eq!(v[a], "a!");
    assert_eq!(v[b], "b", "writing one slot leaves the other alone");
}

#[test]
#[should_panic(expected = "out of bounds")]
fn index_panics_at_len() {
    let mut v: V<u8> = IdVec::new();
    v.push(1);
    let _ = v[Ix(1)];
}

#[test]
#[should_panic(expected = "out of bounds")]
fn index_panics_on_empty() {
    let v: V<u8> = IdVec::new();
    let _ = v[Ix(0)];
}

#[test]
#[should_panic(expected = "out of bounds")]
fn index_mut_panics_at_len() {
    let mut v: V<u8> = IdVec::from_elem(0, 2);
    v[Ix(2)] = 1;
}

#[test]
fn get_at_the_bounds_table() {
    let mut v: V<u8> = IdVec::from_elem(7, 3);
    for (i, expected) in [
        (0, Some(7)),
        (2, Some(7)),
        (3, None),
        (4, None),
        (9000, None),
    ] {
        assert_eq!(v.get(Ix(i)).copied(), expected, "get {i}");
        assert_eq!(v.get_mut(Ix(i)).map(|x| *x), expected, "get_mut {i}");
    }
}

#[test]
fn get_mut_writes_through() {
    let mut v: V<u8> = IdVec::from_elem(0, 2);
    *v.get_mut(Ix(1)).unwrap() = 5;
    assert_eq!(v.as_slice(), [0, 5]);
}

#[test]
fn from_elem_clones_table() {
    for len in [0, 1, 2, 64, 65] {
        let v: V<String> = IdVec::from_elem("x".to_owned(), len);
        assert_eq!(v.len(), len);
        assert!(v.iter().all(|s| s == "x"));
    }
}

#[test]
fn ensure_index_grows_exactly_enough_table() {
    let cases = [
        (0, 0, 1),
        (0, 4, 5),
        (3, 3, 4),
        (3, 2, 3),
        (3, 0, 3),
        (3, 9, 10),
        (1, 1000, 1001),
    ];
    for (start, index, expected) in cases {
        let mut v: V<u32> = IdVec::from_elem(1, start);
        let mut calls = 0;
        v.ensure_index(Ix(index as u32), || {
            calls += 1;
            2
        });
        assert_eq!(v.len(), expected, "{start} {index}");
        assert_eq!(calls, expected - start, "{start} {index}");
        assert!(v.iter().take(start).all(|&x| x == 1), "old values stay");
        assert!(
            v.iter().skip(start).all(|&x| x == 2),
            "new values are filled"
        );
    }
}

#[test]
fn ensure_index_makes_the_index_valid() {
    let mut v: V<u8> = IdVec::new();
    v.ensure_index(Ix(6), || 0);
    v[Ix(6)] = 9;
    assert_eq!(v.get(Ix(6)), Some(&9));
    assert_eq!(v.get(Ix(7)), None);
    assert_eq!(v.push(1), Ix(7));
}

#[test]
fn iter_visits_in_index_order_both_ways() {
    let v: V<u32> = (10..14).collect();
    assert_eq!(v.iter().copied().collect::<Vec<_>>(), [10, 11, 12, 13]);
    assert_eq!(
        v.iter().rev().copied().collect::<Vec<_>>(),
        [13, 12, 11, 10]
    );
    assert_eq!(v.iter().len(), 4);
}

#[test]
fn iter_mut_updates_in_place() {
    let mut v: V<u32> = (0..4).collect();
    for x in v.iter_mut() {
        *x += 100;
    }
    assert_eq!(v.as_slice(), [100, 101, 102, 103]);
}

#[test]
fn iter_enumerated_pairs_typed_indices_with_values() {
    let v: V<char> = "abc".chars().collect();
    let pairs: Vec<(Ix, char)> = v.iter_enumerated().map(|(i, &c)| (i, c)).collect();
    assert_eq!(pairs, [(Ix(0), 'a'), (Ix(1), 'b'), (Ix(2), 'c')]);
    let last = v.iter_enumerated().next_back().map(|(i, &c)| (i, c));
    assert_eq!(last, Some((Ix(2), 'c')));
    assert_eq!(v.iter_enumerated().len(), 3);
}

#[test]
fn iter_enumerated_mut_can_use_the_index() {
    let mut v: V<u32> = IdVec::from_elem(1000, 3);
    for (i, x) in v.iter_enumerated_mut() {
        *x += i.index() as u32;
    }
    assert_eq!(v.as_slice(), [1000, 1001, 1002]);
    assert_eq!(v.iter_enumerated_mut().len(), 3);
    let last = v.iter_enumerated_mut().next_back().map(|(i, x)| (i, *x));
    assert_eq!(last, Some((Ix(2), 1002)));
}

#[test]
fn indices_cover_the_vector_and_allow_mutation() {
    let mut v: V<u32> = IdVec::from_elem(0, 4);
    assert_eq!(v.indices().len(), 4);
    assert_eq!(
        v.indices().collect::<Vec<_>>(),
        [Ix(0), Ix(1), Ix(2), Ix(3)]
    );
    assert_eq!(v.indices().next_back(), Some(Ix(3)));
    for i in v.indices() {
        v[i] = i.0 * 2;
    }
    assert_eq!(v.as_slice(), [0, 2, 4, 6]);
}

#[test]
fn conversions_from_vec_and_iterators() {
    let from_vec: V<u8> = vec![1, 2, 3].into();
    let collected: V<u8> = [1, 2, 3].into_iter().collect();
    assert_eq!(from_vec, collected);
    assert_eq!(from_vec.as_slice(), [1, 2, 3]);
    assert_eq!(from_vec[Ix(2)], 3);
}

#[test]
fn into_iterator_three_ways() {
    let mut v: V<u32> = (1..4).collect();
    let mut sum = 0;
    for x in &v {
        sum += *x;
    }
    assert_eq!(sum, 6);
    for x in &mut v {
        *x *= 2;
    }
    let owned: Vec<u32> = v.into_iter().collect();
    assert_eq!(owned, [2, 4, 6]);
}

#[test]
fn clone_is_independent() {
    let original: V<u8> = vec![1, 2].into();
    let mut copy = original.clone();
    copy[Ix(0)] = 9;
    copy.push(3);
    assert_eq!(original.as_slice(), [1, 2]);
    assert_eq!(copy.as_slice(), [9, 2, 3]);
}

#[test]
fn equality_compares_contents_and_order_table() {
    let cases: &[(&[u8], &[u8], bool)] = &[
        (&[], &[], true),
        (&[1, 2], &[1, 2], true),
        (&[1, 2], &[2, 1], false),
        (&[1, 2], &[1], false),
        (&[], &[0], false),
    ];
    for &(a, b, expected) in cases {
        let a: V<u8> = a.iter().copied().collect();
        let b: V<u8> = b.iter().copied().collect();
        assert_eq!(a == b, expected, "{a:?} {b:?}");
    }
}

#[test]
fn debug_prints_a_list() {
    let v: V<u8> = vec![1, 2].into();
    assert_eq!(format!("{v:?}"), "[1, 2]");
}

#[test]
fn traits_do_not_require_anything_of_the_index() {
    let v: IdVec<Bare, u8> = vec![4, 5].into();
    let copy = v.clone();
    assert!(v == copy);
    assert_eq!(format!("{v:?}"), "[4, 5]");
    assert_eq!(v[Bare(1)], 5);
    let empty: IdVec<Bare, u8> = IdVec::default();
    assert!(empty != v);
}

#[test]
fn file_id_is_an_index_table() {
    for i in [0usize, 1, 7, 1 << 20, u32::MAX as usize] {
        let id = FileId::new(i);
        assert_eq!(id, FileId(i as u32));
        assert_eq!(id.index(), i);
    }
}

#[test]
#[should_panic(expected = "file index exceeds u32")]
fn file_id_rejects_what_does_not_fit() {
    FileId::new(u32::MAX as usize + 1);
}

#[test]
fn file_ids_index_an_id_vec() {
    let mut v: IdVec<FileId, &str> = IdVec::new();
    let a = v.push("a");
    let b = v.push("b");
    assert_eq!((a, b), (FileId(0), FileId(1)));
    assert_eq!(v[b], "b");
}
