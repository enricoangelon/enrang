//! `TargetUsize` and the limits of `DataLayout`, at the 32-bit boundary. Nothing
//! here may assume a 64-bit `usize`.

use enrang_target::{DataLayout, TargetUsize};
use enrang_testkit::Harness;

use crate::support::{TARGETS, backticked, default_spec, line_starting, number, section};

const BOUNDARY: [u64; 11] = [
    0,
    1,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFE,
    0xFFFF_FFFF,
    0x1_0000_0000,
    0x1_0000_0001,
    0x7FFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
    u64::MAX,
];

fn is_32_bit(target: &str) -> bool {
    target.starts_with("i386-") || target == "vm32"
}

pub fn register(h: &mut Harness) {
    boundary(h);
    limits(h);
    spec_examples(h);
}

fn boundary(h: &mut Harness) {
    for target in TARGETS {
        for value in BOUNDARY {
            h.case(format!("usize/{target}/{value:#x}"), move || {
                let spec = default_spec(target);
                let fits = !is_32_bit(target) || value <= 0xFFFF_FFFF;
                let want = fits.then_some(TargetUsize(value));
                assert_eq!(TargetUsize::checked(value, &spec), want);
            });
        }
    }
    h.case("usize/the checked value is the value", || {
        let spec = default_spec("i386-linux");
        let checked = TargetUsize::checked(0xDEAD_BEEF, &spec).expect("it fits");
        assert_eq!(checked.0, 0xDEAD_BEEF);
    });
    h.case("usize/the width comes from the spec, not the host", || {
        // The same value, the same process, opposite answers.
        let value = 0x1_0000_0000;
        assert!(TargetUsize::checked(value, &default_spec("x86_64-linux")).is_some());
        assert!(TargetUsize::checked(value, &default_spec("i386-linux")).is_none());
    });
    h.case(
        "usize/a spec with another layout changes the answer",
        || {
            let mut spec = default_spec("x86_64-linux");
            spec.layout.ptr_bytes = 4;
            assert!(TargetUsize::checked(0x1_0000_0000, &spec).is_none());
            spec.layout.ptr_bytes = 2;
            assert!(TargetUsize::checked(0x1_0000, &spec).is_none());
            assert!(TargetUsize::checked(0xFFFF, &spec).is_some());
        },
    );
}

fn limits(h: &mut Harness) {
    for target in TARGETS {
        h.case(format!("limits/{target}"), move || {
            let layout = default_spec(target).layout;
            let (umax, imax) = if is_32_bit(target) {
                (u64::from(u32::MAX), i32::MAX as u64)
            } else {
                (u64::MAX, i64::MAX as u64)
            };
            assert_eq!(layout.usize_max(), umax);
            assert_eq!(layout.isize_max(), imax);
        });
    }
    h.case("limits/the shift never overflows at P == 8", || {
        // `1 << (8 * P)` would: this is the one place the width can bite.
        let layout = DataLayout {
            ptr_bytes: 8,
            i64_align: 8,
            f64_align: 8,
            frame_align: 16,
        };
        assert_eq!(layout.usize_max(), u64::MAX);
    });
}

/// The values SPEC 11 and TESTING use to show sizes cannot wrap.
fn spec_examples(h: &mut Harness) {
    let line = line_starting(
        section("SPEC.md", "## 11. Runtime data layout"),
        "**Size limits.**",
    );
    let quoted: Vec<&str> = backticked(line);
    let example = |start: &str| -> u64 {
        let ty = quoted
            .iter()
            .find(|piece| piece.starts_with(start))
            .unwrap_or_else(|| panic!("SPEC 11 no longer shows `{start}`"));
        number(array_len(ty))
    };
    let bytes = example("u8[");
    h.case(
        "limits/`u8[3000000000]` is a usize on i386 but over isize.MAX",
        move || {
            assert_eq!(bytes, 3_000_000_000);
            for target in ["i386-linux", "i386-none", "vm32"] {
                let spec = default_spec(target);
                assert!(TargetUsize::checked(bytes, &spec).is_some(), "{target}");
                assert!(bytes > spec.layout.isize_max(), "{target}");
            }
            for target in ["x86_64-linux", "vm64"] {
                assert!(bytes < default_spec(target).layout.isize_max(), "{target}");
            }
        },
    );
    let elements = example("u64[");
    h.case(
        "limits/`u64[536870912]` wraps to 0 in 32 bits, and is refused",
        move || {
            let size = elements * 8;
            assert_eq!(size as u32, 0, "SPEC's point: it would wrap to 0");
            for target in ["i386-linux", "i386-none", "vm32"] {
                assert_eq!(
                    TargetUsize::checked(size, &default_spec(target)),
                    None,
                    "{target}"
                );
            }
            for target in ["x86_64-linux", "vm64"] {
                assert!(
                    TargetUsize::checked(size, &default_spec(target)).is_some(),
                    "{target}"
                );
            }
        },
    );
    h.case(
        "limits/TESTING's `b.reserve(0x80000000)` passes isize.MAX on 32 bits",
        || {
            let text = section("TESTING.md", "## 18. Traceability meta-tests");
            assert!(
                text.contains("`b.reserve(0x80000000)`"),
                "the row has changed"
            );
            let limit = default_spec("vm32").layout.isize_max();
            assert_eq!(limit + 1, 0x8000_0000);
        },
    );
}

/// The `N` of `T[N]`.
fn array_len(ty: &str) -> &str {
    let (_, rest) = ty
        .split_once('[')
        .unwrap_or_else(|| panic!("`{ty}` has no length"));
    rest.trim_end_matches(']')
}
