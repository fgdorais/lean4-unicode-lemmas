/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeBasic
public import Batteries.Data.Char.Basic

public section

namespace Unicode.Ascii
open GeneralCategory

/-! Lean core's `Char` functions only handle ASCII; on ASCII they agree with UnicodeBasic. -/

private theorem of_forall_lt_0x80 {p : Char → Prop} (h : ∀ n : Fin 0x80, p (Char.ofNat n))
    {c : Char} (hc : c.val < 0x80) : p c := by
  have := h ⟨c.toNat, UInt32.lt_iff_toNat_lt.1 hc⟩
  rwa [Char.ofNat_toNat] at this

theorem isUppercase_eq_isUpper {c : Char} (h : c.val < 0x80) : isUppercase c = c.isUpper :=
  of_forall_lt_0x80 (p := fun c => isUppercase c = c.isUpper) (by decide) h

theorem isLowercase_eq_isLower {c : Char} (h : c.val < 0x80) : isLowercase c = c.isLower :=
  of_forall_lt_0x80 (p := fun c => isLowercase c = c.isLower) (by decide) h

theorem isAlphabetic_eq_isAlpha {c : Char} (h : c.val < 0x80) : isAlphabetic c = c.isAlpha :=
  of_forall_lt_0x80 (p := fun c => isAlphabetic c = c.isAlpha) (by decide) h

theorem isDigit_eq_isDigit {c : Char} (h : c.val < 0x80) : isDigit c = c.isDigit :=
  of_forall_lt_0x80 (p := fun c => isDigit c = c.isDigit) (by decide) h

theorem getLowerChar_eq_toLower {c : Char} (h : c.val < 0x80) : getLowerChar c = c.toLower :=
  of_forall_lt_0x80 (p := fun c => getLowerChar c = c.toLower) (by decide +kernel) h

theorem getUpperChar_eq_toUpper {c : Char} (h : c.val < 0x80) : getUpperChar c = c.toUpper :=
  of_forall_lt_0x80 (p := fun c => getUpperChar c = c.toUpper) (by decide +kernel) h

theorem isUppercase_of_isUpper {c : Char} (h : c.isUpper) : isUppercase c := by
  have hc : c.val < 0x80 := by simp [Char.isUpper] at h; grind
  rwa [isUppercase_eq_isUpper hc]

theorem isLowercase_of_isLower {c : Char} (h : c.isLower) : isLowercase c := by
  have hc : c.val < 0x80 := by simp [Char.isLower] at h; grind
  rwa [isLowercase_eq_isLower hc]

theorem isAlphabetic_of_isAlpha {c : Char} (h : c.isAlpha) : isAlphabetic c := by
  have hc : c.val < 0x80 := by simp [Char.isAlpha, Char.isUpper, Char.isLower] at h; grind
  rwa [isAlphabetic_eq_isAlpha hc]

theorem isDigit_of_isDigit {c : Char} (h : c.isDigit) : isDigit c := by
  have hc : c.val < 0x80 := by simp [Char.isDigit] at h; grind
  rwa [isDigit_eq_isDigit hc]

/-- Unicode white space also includes U+000B and U+000C, which core's `Char.isWhitespace` omits. -/
theorem isWhiteSpace_of_isWhitespace {c : Char} : c.isWhitespace → isWhiteSpace c := by
  simp only [Char.isWhitespace, Bool.or_eq_true, decide_eq_true_eq]
  rintro (((rfl | rfl) | rfl) | rfl) <;> decide

end Unicode.Ascii
