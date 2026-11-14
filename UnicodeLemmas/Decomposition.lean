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

theorem getCanonicalCombiningClass_eq_zero_of_lt {c : Char} (h : c.val < 0x80) :
    getCanonicalCombiningClass c = 0 := by
  simp [getCanonicalCombiningClass, h]

theorem getDecompositionMapping?_eq_none_of_lt {c : Char} (h : c.val < 0x80) :
    getDecompositionMapping? c = none := by
  simp [getDecompositionMapping?, h]

theorem getCanonicalDecomposition_eq_of_lt {c : Char} (h : c.val < 0x80) :
    getCanonicalDecomposition c = c.toString := by
  simp [getCanonicalDecomposition, h]

end Unicode
