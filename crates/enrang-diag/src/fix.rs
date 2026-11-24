//! Applying fix-its to a file's text.

use std::error::Error;
use std::fmt;

use enrang_base::BytePos;

use crate::diagnostic::Edit;

/// Why a set of edits could not be applied.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum FixConflict {
    /// The two edits touch the same bytes, or insert at one place in no defined
    /// order. `first` sorts before `second`.
    Overlap { first: Edit, second: Edit },
    /// The span is `DUMMY` or inverted, leaves the text, or splits a character.
    InvalidSpan { edit: Edit },
}

impl fmt::Display for FixConflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FixConflict::Overlap { first, second } => write!(
                f,
                "the edit at {}..{} conflicts with the edit at {}..{}",
                first.span.lo.0, first.span.hi.0, second.span.lo.0, second.span.hi.0,
            ),
            FixConflict::InvalidSpan { edit } => write!(
                f,
                "the edit at {}..{} does not fit this text",
                edit.span.lo.0, edit.span.hi.0,
            ),
        }
    }
}

impl Error for FixConflict {}

/// Applies `edits` to `text`, which starts at global position `base`.
///
/// Order in `edits` does not matter. An edit given twice applies once. An
/// insertion may touch either end of a replacement; it goes before a replacement
/// starting at its position and after one ending there.
pub fn apply_fixes(text: &str, base: BytePos, edits: &[Edit]) -> Result<String, FixConflict> {
    let mut placed = Vec::with_capacity(edits.len());
    for edit in edits {
        let range = byte_range(text, base, edit)
            .ok_or_else(|| FixConflict::InvalidSpan { edit: edit.clone() })?;
        placed.push((range, edit));
    }
    placed.sort_by_key(|&(range, _)| range);
    placed.dedup_by(|later, earlier| later.1 == earlier.1);
    for pair in placed.windows(2) {
        let ((first_lo, first_hi), first) = pair[0];
        let ((second_lo, second_hi), second) = pair[1];
        if second_lo < first_hi || (first_lo, first_hi) == (second_lo, second_hi) {
            return Err(FixConflict::Overlap {
                first: first.clone(),
                second: second.clone(),
            });
        }
    }

    let mut fixed = String::with_capacity(text.len());
    let mut cursor = 0;
    for ((lo, hi), edit) in placed {
        fixed.push_str(&text[cursor..lo]);
        fixed.push_str(&edit.replacement);
        cursor = hi;
    }
    fixed.push_str(&text[cursor..]);
    Ok(fixed)
}

/// The edit's span as offsets into `text`, or `None` if it does not fit.
fn byte_range(text: &str, base: BytePos, edit: &Edit) -> Option<(usize, usize)> {
    if edit.span.is_dummy() {
        return None;
    }
    let lo = edit.span.lo.0.checked_sub(base.0)? as usize;
    let hi = edit.span.hi.0.checked_sub(base.0)? as usize;
    let fits = lo <= hi && text.is_char_boundary(lo) && text.is_char_boundary(hi);
    fits.then_some((lo, hi))
}
