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

/-! Lean core's `Char` functions only handle ASCII; on ASCII they agree with UnicodeBasic. -/

theorem isUppercase_eq_isUpper {c : Char} (h : c.val < 0x80) : isUppercase c = c.isUpper := by
  revert c; native_decide

theorem isLowercase_eq_isLower {c : Char} (h : c.val < 0x80) : isLowercase c = c.isLower := by
  revert c; native_decide

theorem isAlphabetic_eq_isAlpha {c : Char} (h : c.val < 0x80) : isAlphabetic c = c.isAlpha := by
  revert c; native_decide

theorem isDigit_eq_isDigit {c : Char} (h : c.val < 0x80) : isDigit c = c.isDigit := by
  revert c; native_decide

theorem getLowerChar_eq_toLower {c : Char} (h : c.val < 0x80) : getLowerChar c = c.toLower := by
  revert c; native_decide

theorem getUpperChar_eq_toUpper {c : Char} (h : c.val < 0x80) : getUpperChar c = c.toUpper := by
  revert c; native_decide

theorem isUppercase_of_isUpper {c : Char} : c.isUpper → isUppercase c := by
  revert c; native_decide

theorem isLowercase_of_isLower {c : Char} : c.isLower → isLowercase c := by
  revert c; native_decide

theorem isAlphabetic_of_isAlpha {c : Char} : c.isAlpha → isAlphabetic c := by
  revert c; native_decide

theorem isDigit_of_isDigit {c : Char} : c.isDigit → isDigit c := by
  revert c; native_decide

/-- Unicode white space also includes U+000B and U+000C, which core's `Char.isWhitespace` omits. -/
theorem isWhiteSpace_of_isWhitespace {c : Char} : c.isWhitespace → isWhiteSpace c := by
  revert c; native_decide

end Unicode
