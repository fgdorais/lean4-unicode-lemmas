/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeBasic
public import UnicodeLemmas.Char
meta import UnicodeBasic
meta import UnicodeLemmas.Char

public section

namespace Unicode
open GeneralCategory

theorem isCased_of_isUppercase {c : Char} : isUppercase c → isCased c := by
  revert c; native_decide

theorem isCased_of_isLowercase {c : Char} : isLowercase c → isCased c := by
  revert c; native_decide

theorem isUppercase_of_isUppercaseLetter {c : Char} : isUppercaseLetter c → isUppercase c := by
  revert c; native_decide

theorem isLowercase_of_isLowercaseLetter {c : Char} : isLowercaseLetter c → isLowercase c := by
  revert c; native_decide

theorem isCased_of_isCasedLetter {c : Char} : isCasedLetter c → isCased c := by
  revert c; native_decide

theorem isCased_iff {c : Char} :
    isCased c ↔ isUppercase c ∨ isLowercase c ∨ isTitlecaseLetter c := by
  revert c; native_decide

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

theorem getLowerChar_of_not_isCased {c : Char} : ¬ isCased c → getLowerChar c = c := by
  revert c; native_decide

theorem getUpperChar_of_not_isCased {c : Char} : ¬ isCased c → getUpperChar c = c := by
  revert c; native_decide

theorem getTitleChar_of_not_isCased {c : Char} : ¬ isCased c → getTitleChar c = c := by
  revert c; native_decide

theorem getCaseFoldingChar_of_not_isCased {c : Char} : ¬ isCased c → getCaseFoldingChar c = c := by
  revert c; native_decide

end Unicode
