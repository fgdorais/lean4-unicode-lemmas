/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeBasic
public import Batteries.Data.Char.Basic
public import UnicodeLemmas.GeneralCategory
meta import UnicodeBasic
meta import Batteries.Data.Char.Basic

public section

namespace Unicode
open GeneralCategory

/-- A character has numeric type `Decimal` exactly when its general category is `Nd`. -/
theorem isDecimal_eq_isDecimalNumber (c : Char) : isDecimal c = isDecimalNumber c := by
  revert c; native_decide

theorem isDigit_of_isDecimal {c : Char} : isDecimal c → isDigit c := by
  revert c; native_decide

theorem isNumber_of_isDecimal {c : Char} (h : isDecimal c) : isNumber c :=
  isNumber_of_isDecimalNumber (isDecimal_eq_isDecimalNumber c ▸ h)

theorem isNumber_of_isDigit {c : Char} : isDigit c → isNumber c := by
  revert c; native_decide

theorem isNumeric_of_isNumber {c : Char} : isNumber c → isNumeric c := by
  revert c; native_decide

theorem isNumeric_of_isDigit {c : Char} : isDigit c → isNumeric c := by
  simp only [Unicode.isDigit, Unicode.isNumeric]
  split
  · exact id
  · split <;> simp_all

@[simp] theorem isSome_getDigit? (c : Char) : (getDigit? c).isSome = isDigit c := by
  revert c; native_decide

@[simp] theorem isSome_getHexDigit? (c : Char) : (getHexDigit? c).isSome = isHexDigit c := by
  revert c; native_decide

@[simp] theorem isSome_getDecimalRange? (c : Char) :
    (getDecimalRange? c).isSome = isDecimal c := by
  revert c; native_decide

private theorem getDecimalRange?_all (c : Char) : (getDecimalRange? c).all (fun (a, b) =>
    b.toNat == a.toNat + 9 && a ≤ c && c ≤ b && (getDigit? c).map Fin.val == some (c.toNat - a.toNat)
      && (List.range 10).all fun k => getDecimalRange? (Char.ofNat (a.toNat + k)) == some (a, b)) := by
  revert c; native_decide

/-- Decimal digits come in contiguous ranges of ten characters with values `0` to `9`. -/
theorem getDecimalRange?_eq_some {c a b : Char} (h : getDecimalRange? c = some (a, b)) :
    b.toNat = a.toNat + 9 ∧ a ≤ c ∧ c ≤ b ∧ (getDigit? c).map Fin.val = some (c.toNat - a.toNat) ∧
      ∀ k < 10, getDecimalRange? (Char.ofNat (a.toNat + k)) = some (a, b) := by
  have := getDecimalRange?_all c
  simp only [h, Option.all_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at this
  exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩

theorem toNat_snd_of_getDecimalRange?_eq_some {c a b : Char} (h : getDecimalRange? c = some (a, b)) :
    b.toNat = a.toNat + 9 := (getDecimalRange?_eq_some h).1

theorem le_of_getDecimalRange?_eq_some {c a b : Char} (h : getDecimalRange? c = some (a, b)) :
    a ≤ c ∧ c ≤ b := ⟨(getDecimalRange?_eq_some h).2.1, (getDecimalRange?_eq_some h).2.2.1⟩

theorem getDigit?_of_getDecimalRange?_eq_some {c a b : Char} (h : getDecimalRange? c = some (a, b)) :
    (getDigit? c).map Fin.val = some (c.toNat - a.toNat) := (getDecimalRange?_eq_some h).2.2.2.1

end Unicode
