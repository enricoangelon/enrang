//! Size limits (SPEC 11, S:1628) and the checked placement every aggregate uses.
//!
//! No type or static may exceed the target's `isize.MAX` bytes, a `T[N]` may not
//! have `N` above `isize.MAX` whatever the size of `T`, and no stack frame may
//! exceed `2^31 - 1` bytes. Sizes never wrap: every sum and product here is
//! checked in `u64` and compared with the limit, so `u64[536870912]`, whose size is
//! `2^32`, is too large on `i386` rather than 0.

use enrang_target::DataLayout;

use crate::Layout;

/// The largest stack frame on every target: `2^31 - 1` bytes (S:1628).
pub const FRAME_MAX: u64 = (1 << 31) - 1;

/// The largest size of a type or static on a target: its `isize.MAX`.
pub fn max_size(dl: DataLayout) -> u64 {
    dl.isize_max()
}

/// Whether a `T[N]` may have `N` elements on a target, whatever `T` is: `N` at most
/// `isize.MAX`, so `length()` always fits.
pub fn count_fits(dl: DataLayout, count: u64) -> bool {
    count <= dl.isize_max()
}

/// A stack frame being laid out: each local at the next offset aligned for it, in
/// declaration order (plan d.17). The exact frame of the native backend (frame
/// alignment, spills, saved registers) is codegen's at M5.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Frame {
    size: u64,
}

impl Frame {
    pub fn new() -> Frame {
        Frame { size: 0 }
    }

    /// Places a local and returns its offset; `None` when the frame would exceed
    /// [`FRAME_MAX`], which makes that local the one that crosses it (EN0435). A
    /// refused local leaves the frame as it was.
    pub fn push(&mut self, local: &Layout) -> Option<u64> {
        let at = align_up(self.size, local.align)?;
        let end = at.checked_add(local.size)?;
        if end > FRAME_MAX {
            return None;
        }
        self.size = end;
        Some(at)
    }

    /// The bytes placed so far.
    pub fn size(&self) -> u64 {
        self.size
    }
}

/// `offset` rounded up to `align`, a power of two; `None` on overflow.
pub(crate) fn align_up(offset: u64, align: u32) -> Option<u64> {
    let mask = u64::from(align.max(1)) - 1;
    offset.checked_add(mask).map(|end| end & !mask)
}

/// Places fields one after another, each at the next offset aligned for it, or
/// with no padding when packed. Only overflow stops a placement; the limit `max`
/// applies to the finished size, which is never below the end of a field.
pub(crate) struct Placer {
    end: u64,
    align: u32,
    packed: bool,
    max: u64,
}

impl Placer {
    /// An empty value: nothing placed, alignment 1.
    pub(crate) fn new(max: u64, packed: bool) -> Placer {
        Placer::resume(0, 1, max, packed)
    }

    /// A value whose first `end` bytes, aligned to `align`, are already placed: a
    /// subclass after its base, a case after an enum's tag.
    pub(crate) fn resume(end: u64, align: u32, max: u64, packed: bool) -> Placer {
        Placer {
            end,
            align,
            packed,
            max,
        }
    }

    /// Places one field of `size` bytes aligned to `align`; `None` on overflow.
    pub(crate) fn place(&mut self, size: u64, align: u32) -> Option<u64> {
        let at = if self.packed {
            self.end
        } else {
            align_up(self.end, align)?
        };
        self.end = at.checked_add(size)?;
        if !self.packed {
            self.align = self.align.max(align);
        }
        Some(at)
    }

    /// The end of the last field placed.
    pub(crate) fn end(&self) -> u64 {
        self.end
    }

    /// The size, rounded up to the alignment, and the alignment, raised to at least
    /// `min_align`; `None` when the rounded size exceeds the limit.
    pub(crate) fn finish(&self, min_align: u32) -> Option<(u64, u32)> {
        let align = self.align.max(min_align);
        let size = align_up(self.end, align)?;
        (size <= self.max).then_some((size, align))
    }
}
