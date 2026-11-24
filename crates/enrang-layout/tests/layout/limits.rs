//! The size limits of SPEC 11 (S:1628): no type above the target's `isize.MAX`, no
//! `T[N]` with `N` above it whatever `T` is, sizes that never wrap, and no frame
//! above `2^31 - 1` bytes.

use enrang_layout::{FRAME_MAX, Frame, LayoutCx, LayoutError, count_fits, max_size};
use enrang_testkit::Harness;

use crate::support::{World, backticked, spec_says};

const LIMITS: &str = "No type or static may exceed `isize.MAX` bytes of the target, no stack frame may exceed `2^31 - 1` bytes";

const VIOLATIONS: &str = "Violations are EN0435: `u8[3000000000]` on `i386`, `u64[536870912]` whose size would wrap to 0, a 3 GB local on `x86_64`. Sizes never wrap.";

fn too_large(w: &mut World, spelling: &str) {
    let ty = w.ty(spelling);
    assert_eq!(
        w.layout(ty),
        Err(LayoutError::TooLarge { ty }),
        "{spelling} on {}",
        w.tcx.target().name
    );
}

pub fn register(h: &mut Harness) {
    h.case("limits/SPEC's violations", || {
        spec_says(VIOLATIONS);
        let named = backticked(VIOLATIONS);
        assert_eq!(
            named,
            ["u8[3000000000]", "i386", "u64[536870912]", "x86_64"]
        );
        let mut i386 = World::new("i386-linux");
        too_large(&mut i386, &named[0]);
        too_large(&mut i386, &named[2]);
        // On x86_64 both fit.
        let mut x64 = World::new("x86_64-linux");
        let big = x64.ty(&named[0]);
        assert_eq!(x64.size_align(big), (3_000_000_000, 1));
        let wraps = x64.ty(&named[2]);
        assert_eq!(x64.size_align(wraps).0, 1 << 32);
        // A 3 GB local is above the frame limit on every target.
        let mut frame = Frame::new();
        assert_eq!(frame.push(&x64.ok(big)), None);
        assert_eq!(frame.size(), 0);
    });

    h.case("limits/the largest sizes", || {
        spec_says(LIMITS);
        let i386 = World::new("i386-linux");
        let x64 = World::new("x86_64-linux");
        assert_eq!(max_size(i386.tcx.target().layout), (1 << 31) - 1);
        assert_eq!(max_size(x64.tcx.target().layout), (1 << 63) - 1);
        assert_eq!(LayoutCx::new(&i386.tcx).max_size(), (1 << 31) - 1);
        assert_eq!(FRAME_MAX, (1 << 31) - 1);
        assert!(count_fits(i386.tcx.target().layout, (1 << 31) - 1));
        assert!(!count_fits(i386.tcx.target().layout, 1 << 31));
        assert!(count_fits(x64.tcx.target().layout, 1 << 62));
    });

    h.case("limits/u64[268435455] fits on i386", || {
        let mut w = World::new("i386-linux");
        let ty = w.ty("u64[268435455]");
        assert_eq!(w.size_align(ty), (2_147_483_640, 4));
        let exact = w.ty("u8[2147483647]");
        assert_eq!(w.size_align(exact).0, 2_147_483_647);
        too_large(&mut w, "u8[2147483648]");
        too_large(&mut w, "u32[536870912]");
    });

    h.case("limits/N above isize.MAX whatever T is", || {
        let mut w = World::new("i386-linux");
        let fits = w.ty("void[2147483647]");
        assert_eq!(w.size_align(fits), (0, 1));
        too_large(&mut w, "void[2147483648]");
        too_large(&mut w, "{ }[4294967296]");
        let mut x64 = World::new("x86_64-linux");
        let fits = x64.ty("void[9223372036854775807]");
        assert_eq!(x64.size_align(fits), (0, 1));
        too_large(&mut x64, "void[9223372036854775808]");
        // The count is checked before the element, which may have no layout.
        let t = x64.param("T");
        let many = x64.tcx.mk_fixed(t, 1 << 63);
        assert_eq!(x64.layout(many), Err(LayoutError::TooLarge { ty: many }));
    });

    h.case("limits/sizes never wrap on x86_64", || {
        let mut w = World::new("x86_64-linux");
        too_large(&mut w, "u64[4611686018427387904]");
        too_large(&mut w, "u8[9223372036854775807][2]");
        too_large(&mut w, "u8[4294967296][4294967296]");
        let fits = w.ty("u8[4294967296][2147483647]");
        assert_eq!(w.size_align(fits).0, (1 << 32) * ((1 << 31) - 1));
        // Three fields of `isize.MAX` bytes would wrap `u64` itself.
        let max = "u8[9223372036854775807]";
        too_large(&mut w, &format!("[{max}, {max}, {max}]"));
        too_large(&mut w, &format!("{{ a: {max}, b: {max}, c: {max} }}"));
        let class = w.declare(&format!(
            "public final class Huge {{ public a: {max}; public b: {max}; public c: {max}; }}"
        ));
        assert_eq!(w.layout(class), Err(LayoutError::TooLarge { ty: class }));
        let e = w.declare(&format!(
            "public enum Huger {{ A {{ a: {max}, b: {max}, c: {max} }} }}"
        ));
        assert_eq!(w.layout(e), Err(LayoutError::TooLarge { ty: e }));
    });

    h.case("limits/an aggregate crosses the limit", || {
        let mut w = World::new("i386-linux");
        let two = w.declare(
            "public final class Two { public a: u8[1073741824]; public b: u8[1073741824]; }",
        );
        assert_eq!(w.layout(two), Err(LayoutError::TooLarge { ty: two }));
        // The hidden table pointer counts.
        let open = w.declare("public class Open { public a: u8[2147483644]; }");
        assert_eq!(w.layout(open), Err(LayoutError::TooLarge { ty: open }));
        let closed = w.declare("public final class Closed { public a: u8[2147483644]; }");
        assert_eq!(w.size_align(closed).0, 2_147_483_644);
        // Rounding the size up to the alignment counts too.
        let round =
            w.declare("public final class Round { public a: i32[536870911]; public b: u8; }");
        assert_eq!(w.layout(round), Err(LayoutError::TooLarge { ty: round }));
        // A subclass after a base that fits.
        let base = w.declare("public class Base { public a: u8[2147483000]; }");
        assert!(w.layout(base).is_ok());
        let sub = w.declare("public class Sub extends Base { public b: u8[1000]; }");
        assert_eq!(w.layout(sub), Err(LayoutError::TooLarge { ty: sub }));
        // A too-large field names the field's type, not its class.
        let inner = w.ty("u8[3000000000]");
        let holder =
            w.declare("public final class Holder { public x: u8; public big: u8[3000000000]; }");
        assert_eq!(w.layout(holder), Err(LayoutError::TooLarge { ty: inner }));
    });

    h.case("limits/sums and tuples cross the limit", || {
        let mut w = World::new("i386-linux");
        for spelling in [
            "u8[2147483647] | null",
            "[u8[2147483647], u8]",
            "{ a: u8[2147483647], b: bool }",
        ] {
            too_large(&mut w, spelling);
        }
        let e = w.declare("public enum Big { A { data: u8[2147483644] }, B }");
        assert_eq!(w.layout(e), Err(LayoutError::TooLarge { ty: e }));
        let fits = w.declare("public enum Fits { A { data: u8[2147483640] }, B }");
        assert_eq!(w.size_align(fits).0, 2_147_483_644);
        let fits = w.ty("u8[2147483640] | null");
        assert_eq!(w.size_align(fits).0, 2_147_483_644);
        // Its end is at the limit, but rounding up to the tag's alignment is not.
        too_large(&mut w, "u8[2147483643] | null");
    });

    h.case("limits/a frame places locals in order", || {
        let mut w = World::new("x86_64-linux");
        let (byte, wide, text) = (w.ty("u8"), w.ty("i64"), w.ty("string"));
        let mut frame = Frame::new();
        assert_eq!(frame.push(&w.ok(byte)), Some(0));
        assert_eq!(frame.push(&w.ok(wide)), Some(8));
        assert_eq!(frame.push(&w.ok(byte)), Some(16));
        assert_eq!(frame.push(&w.ok(text)), Some(24));
        assert_eq!(frame.size(), 48);
        let mut i386 = World::new("i386-linux");
        let (byte, wide) = (i386.ty("u8"), i386.ty("i64"));
        let mut frame = Frame::new();
        assert_eq!(frame.push(&i386.ok(byte)), Some(0));
        assert_eq!(frame.push(&i386.ok(wide)), Some(4));
    });

    h.case("limits/a frame stops at 2^31 - 1 bytes", || {
        let mut w = World::new("x86_64-linux");
        let half = w.ty("u8[1073741824]");
        let rest = w.ty("u8[1073741823]");
        let byte = w.ty("u8");
        let mut frame = Frame::new();
        assert_eq!(frame.push(&w.ok(half)), Some(0));
        assert_eq!(frame.push(&w.ok(rest)), Some(1 << 30));
        assert_eq!(frame.size(), FRAME_MAX);
        // The local that crosses the limit is refused and changes nothing.
        assert_eq!(frame.push(&w.ok(byte)), None);
        assert_eq!(frame.size(), FRAME_MAX);
        let empty = w.ty("void");
        assert_eq!(frame.push(&w.ok(empty)), Some(FRAME_MAX));
        // Alignment padding counts too.
        let mut frame = Frame::new();
        let odd = w.ty("u8[2147483643]");
        let word = w.ty("u32");
        assert_eq!(frame.push(&w.ok(odd)), Some(0));
        assert_eq!(frame.push(&w.ok(word)), None);
    });
}
