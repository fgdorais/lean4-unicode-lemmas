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

theorem not_isLowercase_of_isUppercase {c : Char} : isUppercase c → ¬ isLowercase c := by
  revert c; native_decide

theorem not_isUppercase_of_isLowercase {c : Char} : isLowercase c → ¬ isUppercase c :=
  fun hl hu => not_isLowercase_of_isUppercase hu hl

@[simp] theorem getLowerChar_getLowerChar (c : Char) :
    getLowerChar (getLowerChar c) = getLowerChar c := by
  revert c; native_decide

@[simp] theorem getUpperChar_getUpperChar (c : Char) :
    getUpperChar (getUpperChar c) = getUpperChar c := by
  revert c; native_decide

@[simp] theorem getCaseFoldingChar_getCaseFoldingChar (c : Char) :
    getCaseFoldingChar (getCaseFoldingChar c) = getCaseFoldingChar c := by
  revert c; native_decide

/-- Simple case mappings leave characters that are not cased unchanged. -/
theorem simpleCaseMappings_of_not_isCased {c : Char} (h : ¬ isCased c) :
    getLowerChar c = c ∧ getUpperChar c = c ∧ getTitleChar c = c ∧ getCaseFoldingChar c = c := by
  revert c h; native_decide

theorem getLowerChar_of_not_isCased {c : Char} (h : ¬ isCased c) : getLowerChar c = c :=
  (simpleCaseMappings_of_not_isCased h).1

theorem getUpperChar_of_not_isCased {c : Char} (h : ¬ isCased c) : getUpperChar c = c :=
  (simpleCaseMappings_of_not_isCased h).2.1

theorem getTitleChar_of_not_isCased {c : Char} (h : ¬ isCased c) : getTitleChar c = c :=
  (simpleCaseMappings_of_not_isCased h).2.2.1

theorem getCaseFoldingChar_of_not_isCased {c : Char} (h : ¬ isCased c) :
    getCaseFoldingChar c = c :=
  (simpleCaseMappings_of_not_isCased h).2.2.2

end Unicode
