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

namespace GC

@[simp] theorem subset_refl (x : GC) : x ⊆ x :=
  beq_iff_eq.2 (UInt32.and_self (a := x))

private theorem and_eq_of_and_eq {x y z : UInt32} (h₁ : x &&& y = x) (h₂ : y &&& z = y) :
    x &&& z = x := by
  rw [← h₁, UInt32.and_assoc, h₂]

theorem subset_trans {x y z : GC} (h₁ : x ⊆ y) (h₂ : y ⊆ z) : x ⊆ z := by
  have h₁ : x &&& y = x := beq_iff_eq.1 h₁
  have h₂ : y &&& z = y := beq_iff_eq.1 h₂
  exact beq_iff_eq.2 (and_eq_of_and_eq h₁ h₂)

theorem mem_of_subset_of_mem {c : Char} {x y : GC} (h : x ⊆ y) : c ∈ x → c ∈ y :=
  fun hc => subset_trans hc h

end GC

/-- The general category of a character is exactly one of the 30 basic categories. -/
theorem getGC_mem (c : Char) : getGC c ∈ [GC.Lu, GC.Ll, GC.Lt, GC.Lm, GC.Lo, GC.Mn, GC.Mc, GC.Me,
    GC.Nd, GC.Nl, GC.No, GC.Pc, GC.Pd, GC.Ps, GC.Pe, GC.Pi, GC.Pf, GC.Po, GC.Sm, GC.Sc, GC.Sk,
    GC.So, GC.Zs, GC.Zl, GC.Zp, GC.Cc, GC.Cf, GC.Cs, GC.Co, GC.Cn] := by
  revert c; native_decide

namespace GeneralCategory

theorem isCasedLetter_iff {c : Char} :
    isCasedLetter c ↔ isUppercaseLetter c ∨ isLowercaseLetter c ∨ isTitlecaseLetter c := by
  simp only [isCasedLetter, isUppercaseLetter, isLowercaseLetter, isTitlecaseLetter,
    decide_eq_true_eq]
  show getGC c ⊆ GC.LC ↔ getGC c ⊆ GC.Lu ∨ getGC c ⊆ GC.Ll ∨ getGC c ⊆ GC.Lt
  generalize getGC c = g, getGC_mem c = h
  revert g; decide

/-- No character is a surrogate. -/
@[simp] theorem isSurrogate_eq_false (c : Char) : isSurrogate c = false := by
  revert c; native_decide

local macro "gc_subset" : tactic =>
  `(tactic| (simp only [decide_eq_true_eq]; exact GC.mem_of_subset_of_mem (by decide)))

theorem isCasedLetter_of_isUppercaseLetter {c : Char} :
    isUppercaseLetter c → isCasedLetter c := by gc_subset
theorem isCasedLetter_of_isLowercaseLetter {c : Char} :
    isLowercaseLetter c → isCasedLetter c := by gc_subset
theorem isCasedLetter_of_isTitlecaseLetter {c : Char} :
    isTitlecaseLetter c → isCasedLetter c := by gc_subset
theorem isLetter_of_isCasedLetter {c : Char} : isCasedLetter c → isLetter c := by gc_subset
theorem isLetter_of_isModifierLetter {c : Char} : isModifierLetter c → isLetter c := by gc_subset
theorem isLetter_of_isOtherLetter {c : Char} : isOtherLetter c → isLetter c := by gc_subset

theorem isMark_of_isNonspacingMark {c : Char} : isNonspacingMark c → isMark c := by gc_subset
theorem isMark_of_isSpacingMark {c : Char} : isSpacingMark c → isMark c := by gc_subset
theorem isMark_of_isEnclosingMark {c : Char} : isEnclosingMark c → isMark c := by gc_subset

theorem isNumber_of_isDecimalNumber {c : Char} : isDecimalNumber c → isNumber c := by gc_subset
theorem isNumber_of_isLetterNumber {c : Char} : isLetterNumber c → isNumber c := by gc_subset
theorem isNumber_of_isOtherNumber {c : Char} : isOtherNumber c → isNumber c := by gc_subset

theorem isPunctuation_of_isConnectorPunctuation {c : Char} :
    isConnectorPunctuation c → isPunctuation c := by gc_subset
theorem isPunctuation_of_isDashPunctuation {c : Char} :
    isDashPunctuation c → isPunctuation c := by gc_subset
theorem isGroupPunctuation_of_isOpenPunctuation {c : Char} :
    isOpenPunctuation c → isGroupPunctuation c := by gc_subset
theorem isGroupPunctuation_of_isClosePunctuation {c : Char} :
    isClosePunctuation c → isGroupPunctuation c := by gc_subset
theorem isPunctuation_of_isGroupPunctuation {c : Char} :
    isGroupPunctuation c → isPunctuation c := by gc_subset
theorem isQuotePunctuation_of_isInitialPunctuation {c : Char} :
    isInitialPunctuation c → isQuotePunctuation c := by gc_subset
theorem isQuotePunctuation_of_isFinalPunctuation {c : Char} :
    isFinalPunctuation c → isQuotePunctuation c := by gc_subset
theorem isPunctuation_of_isQuotePunctuation {c : Char} :
    isQuotePunctuation c → isPunctuation c := by gc_subset
theorem isPunctuation_of_isOtherPunctuation {c : Char} :
    isOtherPunctuation c → isPunctuation c := by gc_subset

theorem isSymbol_of_isMathSymbol {c : Char} : isMathSymbol c → isSymbol c := by gc_subset
theorem isSymbol_of_isCurrencySymbol {c : Char} : isCurrencySymbol c → isSymbol c := by gc_subset
theorem isSymbol_of_isModifierSymbol {c : Char} : isModifierSymbol c → isSymbol c := by gc_subset
theorem isSymbol_of_isOtherSymbol {c : Char} : isOtherSymbol c → isSymbol c := by gc_subset

theorem isSeparator_of_isSpaceSeparator {c : Char} :
    isSpaceSeparator c → isSeparator c := by gc_subset
theorem isSeparator_of_isLineSeparator {c : Char} :
    isLineSeparator c → isSeparator c := by gc_subset
theorem isSeparator_of_isParagraphSeparator {c : Char} :
    isParagraphSeparator c → isSeparator c := by gc_subset

theorem isOther_of_isControl {c : Char} : isControl c → isOther c := by gc_subset
theorem isOther_of_isFormat {c : Char} : isFormat c → isOther c := by gc_subset
theorem isOther_of_isSurrogate {c : Char} : isSurrogate c → isOther c := by gc_subset
theorem isOther_of_isPrivateUse {c : Char} : isPrivateUse c → isOther c := by gc_subset
theorem isOther_of_isUnassigned {c : Char} : isUnassigned c → isOther c := by gc_subset

end GeneralCategory

end Unicode
