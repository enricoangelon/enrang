//! Stable item paths (ARCHITECTURE 6.8): their order and how they print.

use enrang_base::intern;
use enrang_hir::{ItemPath, ModulePath};
use enrang_testkit::Harness;

fn path(module: &str, segments: &[&str]) -> ItemPath {
    ItemPath {
        module: ModulePath::new(module),
        segments: segments.iter().map(|s| intern(s)).collect(),
        overload: None,
    }
}

pub fn register(h: &mut Harness) {
    h.case("paths/order: module, then segments, then overload", || {
        // Interned in an order unlike the text order, so ids cannot decide.
        let zeta = path("zeta", &["a"]);
        let alpha = path("alpha", &["z"]);
        let alpha_member = path("alpha", &["z", "m"]);
        let alpha_b = path("alpha", &["b"]);
        let module = ItemPath::module(ModulePath::new("alpha"));
        let mut paths = vec![
            zeta.clone(),
            alpha.clone(),
            alpha_member.clone(),
            alpha_b.clone(),
            module.clone(),
        ];
        let overload_i64 = alpha.clone().with_overload(vec!["i64".to_owned()]);
        let overload_bool = alpha.clone().with_overload(vec!["bool".to_owned()]);
        paths.push(overload_i64.clone());
        paths.push(overload_bool.clone());
        paths.sort();
        assert_eq!(
            paths,
            [
                module,
                alpha_b,
                alpha.clone(),
                overload_bool,
                overload_i64,
                alpha_member,
                zeta
            ]
        );
    });
    h.case("paths/display", || {
        let p = path("src/main", &["Animal", "speak"]);
        assert_eq!(p.to_string(), "src/main::Animal::speak");
        let o =
            path("core/mem", &["swap"]).with_overload(vec!["&i64".to_owned(), "&i64".to_owned()]);
        assert_eq!(o.to_string(), "core/mem::swap(&i64, &i64)");
        assert_eq!(
            ItemPath::module(ModulePath::new("util")).to_string(),
            "util"
        );
    });
    h.case("paths/children and special segments", || {
        let class = ItemPath::item(ModulePath::new("src/main"), intern("Animal"));
        let ctor = class.child(intern(enrang_hir::CTOR_SEGMENT));
        assert_eq!(ctor.to_string(), "src/main::Animal::#ctor");
        assert_eq!(ctor.name(), Some(intern("#ctor")));
        assert_eq!(ItemPath::extend_segment(2).as_str(), "#extend2");
        assert_eq!(ItemPath::test_segment(0).as_str(), "#test0");
    });
    h.case("paths/library modules", || {
        for (path, library) in [
            ("core", true),
            ("core/mem", true),
            ("alloc/array", true),
            ("os/linux_x64/fs", true),
            ("src/main", false),
            ("corefoo", false),
            ("util", false),
        ] {
            assert_eq!(ModulePath::new(path).is_library(), library, "{path}");
        }
    });
}
