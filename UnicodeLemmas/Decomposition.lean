/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeBasic
public import Batteries.Data.Char.Basic
meta import UnicodeBasic
meta import Batteries.Data.Char.Basic

public section

namespace Unicode
open GeneralCategory

theorem getCanonicalCombiningClass_le (c : Char) : getCanonicalCombiningClass c ≤ 254 := by
  revert c; native_decide

/-- Only nonspacing and spacing marks have a nonzero canonical combining class. -/
theorem isNonspacingMark_or_isSpacingMark_of_getCanonicalCombiningClass_ne_zero {c : Char} :
    getCanonicalCombiningClass c ≠ 0 → isNonspacingMark c ∨ isSpacingMark c := by
  revert c; native_decide

private theorem of_forall_lt_0x80 {p : Char → Prop} (h : ∀ n : Fin 0x80, p (Char.ofNat n))
    {c : Char} (hc : c.val < 0x80) : p c := by
  have := h ⟨c.toNat, UInt32.lt_iff_toNat_lt.1 hc⟩
  rwa [Char.ofNat_toNat] at this

theorem getCanonicalCombiningClass_eq_zero_of_lt {c : Char} (h : c.val < 0x80) :
    getCanonicalCombiningClass c = 0 :=
  of_forall_lt_0x80 (p := fun c => getCanonicalCombiningClass c = 0) (by decide +kernel) h

theorem getDecompositionMapping?_eq_none_of_lt {c : Char} (h : c.val < 0x80) :
    getDecompositionMapping? c = none :=
  of_forall_lt_0x80 (p := fun c => getDecompositionMapping? c = none) (by native_decide) h

theorem getCanonicalDecomposition_eq_of_lt {c : Char} (h : c.val < 0x80) :
    getCanonicalDecomposition c = c.toString :=
  of_forall_lt_0x80 (p := fun c => getCanonicalDecomposition c = c.toString) (by decide +kernel) h

end Unicode
