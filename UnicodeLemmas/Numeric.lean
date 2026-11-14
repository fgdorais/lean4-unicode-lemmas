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

end Unicode
