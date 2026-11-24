// Twin of NLL problem case #3, SPEC 5.3's `getOrInsert` (TESTING 13; corpus row
// NLL-3). Enrang accepts it: on the path that inserts, `hit` is dead, so its loan
// is not held there (ARCHITECTURE 6.6). rustc rejects both twins of the writable
// result, because the loan of a reference returned on one path lasts for the
// whole function.
//
// `getOrInsert` returns a writable `&Entry` from `m`, so it has two twins (TESTING
// 13): `get_or_insert` returning `&Entry` and `get_or_insert_mut` returning `&mut
// Entry`; `Table.find` and `Table.last` have two each as well.

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order).
struct Entry {
    hits: i64,
    key: i64,
}

struct Table {
    entries: Vec<Entry>,
}

impl Table {
    fn find(&self, k: i64) -> Option<&Entry> {
        self.entries.iter().find(|e| e.key == k)
    }

    fn find_mut(&mut self, k: i64) -> Option<&mut Entry> {
        self.entries.iter_mut().find(|e| e.key == k)
    }

    fn insert(&mut self, k: i64) {
        self.entries.push(Entry { hits: 0, key: k });
    }

    fn last(&self) -> &Entry {
        &self.entries[self.entries.len() - 1]
    }

    fn last_mut(&mut self) -> &mut Entry {
        let n = self.entries.len();
        &mut self.entries[n - 1]
    }
}

// public function getOrInsert(m: &Table, k: i64): &Entry {
//   const hit = m.find(k);  // NLL problem case #3
//   if (hit != null) { return hit; }
//   m.insert(k);
//   return m.last();
// }
fn get_or_insert(m: &mut Table, k: i64) -> &Entry {
    let hit = m.find(k);
    if let Some(hit) = hit {
        return hit;
    }
    m.insert(k);
    m.last()
}

fn get_or_insert_mut(m: &mut Table, k: i64) -> &mut Entry {
    let hit = m.find_mut(k);
    if let Some(hit) = hit {
        return hit;
    }
    m.insert(k);
    m.last_mut()
}

fn main() {
    let mut t = Table {
        entries: Vec::new(),
    };
    get_or_insert_mut(&mut t, 1).hits += 1;
    get_or_insert_mut(&mut t, 1).hits += 1;
    println!("{}", get_or_insert(&mut t, 1).hits);
}
