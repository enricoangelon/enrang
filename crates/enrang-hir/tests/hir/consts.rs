//! Constant values compared by value (`ConstValue::cmp_numeric`, `as_i128`): the
//! derived `Ord` compares stored bits, which put a negative integer above every
//! positive one, so `match` ranges, interval covers and const eval read these.

use std::cmp::Ordering;

use enrang_hir::{ConstValue, Ty};
use enrang_testkit::Harness;

use crate::support::World;

/// `value` as `ty`'s two's-complement bits at `bits` width, zero-extended, as
/// `ConstValue::Int` stores it.
fn int(value: i128, bits: u32, ty: Ty) -> ConstValue {
    let mask = if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    };
    ConstValue::Int((value as u128) & mask, ty)
}

pub fn register(h: &mut Harness) {
    h.case("consts/a negative signed integer is below zero", || {
        let w = World::new();
        let i32 = w.tcx.common().i32;
        let (minus_ten, zero) = (int(-10, 32, i32), int(0, 32, i32));
        assert_eq!(minus_ten, ConstValue::Int(0xFFFF_FFF6, i32));
        assert!(minus_ten > zero, "the derived order is only for map keys");
        assert_eq!(minus_ten.cmp_numeric(&zero, &w.tcx), Some(Ordering::Less));
        assert_eq!(minus_ten.as_i128(&w.tcx), Some(-10));
        let i8 = w.tcx.common().i8;
        assert_eq!(int(-128, 8, i8).as_i128(&w.tcx), Some(-128));
        assert_eq!(int(127, 8, i8).as_i128(&w.tcx), Some(127));
        let i64 = w.tcx.common().i64;
        assert_eq!(
            int(i128::from(i64::MIN), 64, i64).as_i128(&w.tcx),
            Some(i128::from(i64::MIN))
        );
    });
    h.case("consts/an unsigned integer keeps its bits", || {
        let w = World::new();
        let u32 = w.tcx.common().u32;
        let big = ConstValue::Int(0xFFFF_FFF6, u32);
        assert_eq!(big.as_i128(&w.tcx), Some(0xFFFF_FFF6));
        assert_eq!(
            big.cmp_numeric(&ConstValue::Int(0, u32), &w.tcx),
            Some(Ordering::Greater)
        );
        let u64 = w.tcx.common().u64;
        assert_eq!(
            ConstValue::Int(u128::from(u64::MAX), u64).as_i128(&w.tcx),
            Some(i128::from(u64::MAX))
        );
    });
    h.case("consts/isize follows the target's pointer width", || {
        for (target, bits) in [("i386-linux", 32), ("x86_64-linux", 64)] {
            let w = World::for_target(target);
            let isize = w.tcx.common().isize;
            let minus_one = int(-1, bits, isize);
            assert_eq!(minus_one.as_i128(&w.tcx), Some(-1), "{target}");
            let usize = w.tcx.common().usize;
            assert_eq!(
                int(-1, bits, usize).as_i128(&w.tcx),
                Some((1i128 << bits) - 1),
                "{target}"
            );
        }
    });
    h.case("consts/floats compare by value, NaN with nothing", || {
        let w = World::new();
        let (f32, f64) = (w.tcx.common().f32, w.tcx.common().f64);
        let a = ConstValue::Float(u64::from((-1.5f32).to_bits()), f32);
        let b = ConstValue::Float(u64::from(0.25f32.to_bits()), f32);
        assert_eq!(a.cmp_numeric(&b, &w.tcx), Some(Ordering::Less));
        let c = ConstValue::Float((-2.0f64).to_bits(), f64);
        let d = ConstValue::Float(3.0f64.to_bits(), f64);
        assert_eq!(c.cmp_numeric(&d, &w.tcx), Some(Ordering::Less));
        let nan = ConstValue::Float(f64::NAN.to_bits(), f64);
        assert_eq!(nan.cmp_numeric(&d, &w.tcx), None);
        assert_eq!(
            ConstValue::Bool(false).cmp_numeric(&ConstValue::Bool(true), &w.tcx),
            Some(Ordering::Less)
        );
        assert_eq!(
            ConstValue::Void.cmp_numeric(&ConstValue::Void, &w.tcx),
            None
        );
        assert_eq!(ConstValue::Bool(true).as_i128(&w.tcx), None);
    });
}
