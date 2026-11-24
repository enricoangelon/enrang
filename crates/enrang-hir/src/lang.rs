//! The lang-item table (ARCHITECTURE 10): every item the compiler names, declared
//! in the library with `@lang("name")`.
//!
//! `define_lang_items!` generates [`LangItem`] with its name table, the library
//! layer that declares each item and the milestone from which it must exist. TESTING
//! 18 wants each item "in every target's module graph", which an `os/none` item cannot
//! be (plan doc gap G5), so the check is per layer: an `OsNone` item in the graphs of
//! the freestanding targets only.

use std::fmt;

use enrang_diag::Milestone;

/// The library layer that declares a lang item.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum LangLayer {
    Core,
    Alloc,
    OsNone,
}

impl LangLayer {
    /// The library folder of the layer.
    pub fn folder(self) -> &'static str {
        match self {
            LangLayer::Core => "core",
            LangLayer::Alloc => "alloc",
            LangLayer::OsNone => "os/none",
        }
    }
}

macro_rules! define_lang_items {
    ($($variant:ident $name:literal $layer:ident $since:ident,)*) => {
        /// An item the compiler names (`@lang("name")`).
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
        pub enum LangItem {
            $($variant,)*
        }

        impl LangItem {
            /// Every lang item, in table order.
            pub const ALL: &'static [LangItem] = &[$(LangItem::$variant,)*];

            /// The `@lang("...")` argument.
            pub fn name(self) -> &'static str {
                match self {
                    $(LangItem::$variant => $name,)*
                }
            }

            /// The layer whose modules declare it.
            pub fn layer(self) -> LangLayer {
                match self {
                    $(LangItem::$variant => LangLayer::$layer,)*
                }
            }

            /// The milestone from which the library must declare it.
            pub fn since(self) -> Milestone {
                match self {
                    $(LangItem::$variant => Milestone::$since,)*
                }
            }
        }
    };
}

define_lang_items! {
    Str "string" Core M2,
    Slice "slice" Core M2,
    Result "result" Core M2,
    Failure "failure" Core M2,
    Ok "ok" Core M2,
    Copy "copy" Core M2,
    Clone "clone" Core M2,
    Eq "eq" Core M2,
    Ord "ord" Core M2,
    Display "display" Core M2,
    Error "error" Core M2,
    Formatter "formatter" Core M2,
    Overflowing "overflowing" Core M2,
    Int "int" Core M2,
    Float "float" Core M2,
    VolatileValue "volatile_value" Core M2,
    AtomicValue "atomic_value" Core M2,
    AtomicBits "atomic_bits" Core M2,
    Array "array" Alloc M2,
    Boxed "box" Alloc M2,
    GlobalAllocator "global_allocator" Alloc M2,
    InterruptHandler "interrupt_handler" OsNone M2,
    InterruptFrame "interrupt_frame" OsNone M2,
    BootInfo "boot_info" OsNone M2,
    PanicInfo "panic_info" OsNone M2,
    RtAlloc "rt_alloc" Alloc M3,
    RtDealloc "rt_dealloc" Alloc M3,
    ArrayPush "array_push" Alloc M3,
    ArrayExtendCloned "array_extend_cloned" Alloc M3,
    FailureFromDisplay "failure_from_display" Alloc M3,
    Start "start" Core M3,
    MemReplace "mem_replace" Core M3,
    MemSwap "mem_swap" Core M3,
}

impl LangItem {
    /// The item named `name` in `@lang("name")`.
    pub fn from_name(name: &str) -> Option<LangItem> {
        LangItem::ALL
            .iter()
            .copied()
            .find(|item| item.name() == name)
    }

    /// The sealed interfaces, whose implementers are the compiler's table
    /// (SPEC 4.4 "Sealed bounds"): `__Int`, `__Float`, `VolatileValue`,
    /// `AtomicValue`, `AtomicBits`.
    pub fn is_sealed(self) -> bool {
        matches!(
            self,
            LangItem::Int
                | LangItem::Float
                | LangItem::VolatileValue
                | LangItem::AtomicValue
                | LangItem::AtomicBits
        )
    }
}

impl fmt::Display for LangItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}
