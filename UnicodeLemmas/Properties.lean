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

theorem isAlphabetic_of_isCased {c : Char} : isCased c → isAlphabetic c := by
  revert c; native_decide

theorem isAlphabetic_of_isLetter {c : Char} : isLetter c → isAlphabetic c := by
  revert c; native_decide

theorem isAlphabetic_of_isLetterNumber {c : Char} : isLetterNumber c → isAlphabetic c := by
  revert c; native_decide

theorem isMath_of_isMathSymbol {c : Char} : isMathSymbol c → isMath c := by
  revert c; native_decide

theorem isWhiteSpace_of_isSeparator {c : Char} : isSeparator c → isWhiteSpace c := by
  revert c; native_decide

theorem isSeparator_or_isControl_of_isWhiteSpace {c : Char} :
    isWhiteSpace c → isSeparator c ∨ isControl c := by
  revert c; native_decide

theorem isUnassigned_of_isNoncharacterCodePoint {c : Char} :
    isNoncharacterCodePoint c → isUnassigned c := by
  revert c; native_decide

end Unicode
