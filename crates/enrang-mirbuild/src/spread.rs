//! Array spread (A:965-969; M3 plan c.14; owner 2C): `ArrayBuild` through
//! `AllocArray` and the array's own pushes.
//!
//! `_out: T[]` starts empty, its drop scheduled with the statement, so a `?` in a
//! later part drops what was built. Each part, left to right: an item is pushed
//! (`@lang("array_push")`); a spread's operand, borrowed by its adjust, is viewed as
//! a `&Slice<T>` (`ArrayToSlice` or `FixedToSlice`, none for a view) and appended by
//! `@lang("array_extend_cloned")`; each call takes `&_out [auto-borrow]` after its
//! argument. Then `_out` moves into the destination.

use enrang_base::Span;
use enrang_hir::{ArrayPart, FnRef, LangItem, Ty};
use enrang_mir::{BorrowOrigin, Callee, IntrinsicKind, Operand, Place, Rvalue, StatementKind};

use crate::builder::Builder;
use crate::matches::{borrow, call, op_ty, read, slice_conv, temp, to_temp, value_temp};

/// Lowers `[a, ...b, c]` of element type `elem` into `dest` (A:965).
pub fn lower_array_build(b: &mut Builder, elem: Ty, parts: &[ArrayPart], dest: Place, span: Span) {
    let tcx = b.cx.tcx;
    let (arr, void) = (tcx.mk_array(elem), tcx.common().void);
    let out = temp(b, arr, span);
    let alloc = StatementKind::Intrinsic {
        kind: IntrinsicKind::AllocArray(elem),
        args: Vec::new(),
        dest: Some(out),
    };
    b.push(alloc, span);
    let method = |item| FnRef {
        def: tcx.lang(item),
        args: tcx.intern_list(&[elem]),
    };
    for part in parts {
        let (item, arg, at) = match part {
            ArrayPart::Item(e) => {
                let v = value_temp(b, e);
                (LangItem::ArrayPush, read(b, v), e.span)
            }
            ArrayPart::Spread(e, _) => {
                let s = b.as_operand(e);
                let view = match slice_conv(b, op_ty(b, &s)) {
                    Some(k) => {
                        let t = tcx.mk_ref(tcx.mk_slice(elem));
                        Operand::Move(to_temp(b, Rvalue::Convert(k, s), t, e.span))
                    }
                    None => s,
                };
                (LangItem::ArrayExtendCloned, view, e.span)
            }
        };
        let r = to_temp(
            b,
            borrow(out, BorrowOrigin::AutoBorrow),
            tcx.mk_ref(arr),
            at,
        );
        let d = temp(b, void, at);
        let args = vec![Operand::Move(r), arg];
        call(b, Callee::Fn(method(item)), args, d, at);
    }
    b.assign(dest, Rvalue::Use(Operand::Move(out)), span);
}
