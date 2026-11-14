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

theorem isCased_iff {c : Char} :
    isCased c ↔ isUppercase c ∨ isLowercase c ∨ isTitlecaseLetter c := by
  revert c; native_decide

theorem isCased_of_isUppercase {c : Char} (h : isUppercase c) : isCased c :=
  isCased_iff.2 (.inl h)

theorem isCased_of_isLowercase {c : Char} (h : isLowercase c) : isCased c :=
  isCased_iff.2 (.inr (.inl h))

theorem isCased_of_isTitlecaseLetter {c : Char} (h : isTitlecaseLetter c) : isCased c :=
  isCased_iff.2 (.inr (.inr h))

theorem isUppercase_of_isUppercaseLetter {c : Char} : isUppercaseLetter c → isUppercase c := by
  revert c; native_decide

theorem isLowercase_of_isLowercaseLetter {c : Char} : isLowercaseLetter c → isLowercase c := by
  revert c; native_decide

theorem isCased_of_isCasedLetter {c : Char} (h : isCasedLetter c) : isCased c := by
  match isCasedLetter_iff.1 h with
  | .inl h => exact isCased_of_isUppercase (isUppercase_of_isUppercaseLetter h)
  | .inr (.inl h) => exact isCased_of_isLowercase (isLowercase_of_isLowercaseLetter h)
  | .inr (.inr h) => exact isCased_of_isTitlecaseLetter h

end Unicode
