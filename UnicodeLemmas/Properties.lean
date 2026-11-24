/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeBasic
public import Batteries.Data.Char.Basic
public import UnicodeLemmas.Case
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

theorem isAlphabetic_of_isLowercase {c : Char} (h : isLowercase c) : isAlphabetic c :=
  isAlphabetic_of_isCased (isCased_of_isLowercase h)

theorem isAlphabetic_of_isUppercase {c : Char} (h : isUppercase c) : isAlphabetic c :=
  isAlphabetic_of_isCased (isCased_of_isUppercase h)

theorem isNoncharacterCodePoint_iff {c : Char} : isNoncharacterCodePoint c ↔
    c.val &&& 0xFFFE = 0xFFFE ∨ 0xFDD0 ≤ c.val ∧ c.val ≤ 0xFDEF := by
  have := c.valid
  simp only [isNoncharacterCodePoint, lookupNoncharacterCodePoint, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  grind

/-- The script of a character, unless it is `Zyyy` or `Zinh`, is among its script extensions. -/
theorem contains_getScriptSet_getScript {c : Char} (h₁ : (getScript c).toAbbrev ≠ "Zyyy")
    (h₂ : (getScript c).toAbbrev ≠ "Zinh") : (getScriptSet c).contains (getScript c) := by
  revert c; native_decide

end Unicode
