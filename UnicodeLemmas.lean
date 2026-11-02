/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Batteries
import UnicodeBasic

theorem List.mem_finRange (x : Fin n) : x ∈ finRange n := by
  simp [finRange]

namespace Char

protected def all (p : Char → Bool) : Bool :=
  Nat.all 1114112 fun c h =>
    if h₁ : c < 55296 then
      p (Char.ofNatAux c <| .inl h₁)
    else if h₂ : 57343 < c then
      p (Char.ofNatAux c <| .inr ⟨h₂, h⟩)
    else
      true

private theorem of_all_aux (h : Char.all p) (n : Nat) (hn : n.isValidChar) :
    p (.ofNatAux n hn) := by
  simp [Char.all, Nat.all_eq_finRange_all, -Nat.all_succ] at h
  simp [Nat.isValidChar] at hn
  match hn with
  | .inl hn =>
    have hn' : n < 1114112 := by omega
    have := h ⟨n, hn'⟩ (List.mem_finRange _)
    rwa [dif_pos hn] at this
  | .inr ⟨hn, hn'⟩ =>
    have hn'' : ¬ n < 55296 := by omega
    have := h ⟨n, hn'⟩ (List.mem_finRange _)
    rwa [dif_neg hn'', dif_pos hn] at this

theorem of_all (h : Char.all p) (c : Char) : p c := by
  have : c.toNat.isValidChar := c.valid
  rw [← c.ofNat_toNat, ofNat, dif_pos this]
  exact of_all_aux h c.toNat this

end Char

namespace Unicode

theorem isAlphabetic_of_isCased {c : Char} (h : isCased c) : isAlphabetic c := by
  have : ∀ c, !isCased c || isAlphabetic c := Char.of_all <| by native_decide
  simp [← Bool.not_eq_true, Classical.or_iff_not_imp_left] at this
  exact this c h
