/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeExtra.Normalization
public import Batteries.Data.Char.Basic
public import Batteries.Data.List.Lemmas
meta import UnicodeExtra.Normalization
meta import Batteries.Data.Char.Basic

public section

namespace Unicode
namespace Normalization

/-! ### Insertion of a character in canonical order

These lemmas work on buffers listed backwards, last character first. -/

/-- Relation between a character and the character before it in canonical order -/
private abbrev RevRel (b a : Char × Nat) : Prop := b.2 = 0 ∨ a.2 ≤ b.2

/-- Insert a character into a buffer listed backwards -/
private def insR : List (Char × Nat) → Char × Nat → List (Char × Nat)
  | [], x => [x]
  | y :: rl, x => if x.2 ≠ 0 ∧ x.2 < y.2 then y :: insR rl x else x :: y :: rl

private theorem perm_insR (rl : List (Char × Nat)) (x : Char × Nat) : (insR rl x).Perm (x :: rl) := by
  induction rl with
  | nil => simp [insR]
  | cons y rl ih =>
    simp only [insR]
    split
    · exact (ih.cons y).trans (List.Perm.swap x y rl)
    · exact List.Perm.refl _

private theorem head?_insR (rl : List (Char × Nat)) (x : Char × Nat) :
    (insR rl x).head? = some x ∨ (insR rl x).head? = rl.head? := by
  cases rl with
  | nil => simp [insR]
  | cons y rl => simp only [insR]; split <;> simp

private theorem isChain_insR {rl : List (Char × Nat)} (h : rl.IsChain RevRel) (x : Char × Nat) :
    (insR rl x).IsChain RevRel := by
  induction rl with
  | nil => simp [insR]
  | cons y rl ih =>
    simp only [insR]
    split
    · next hx =>
      have ih := ih (List.isChain_of_isChain_cons h)
      cases hi : insR rl x with
      | nil => simp
      | cons z l =>
        rw [hi] at ih
        refine List.IsChain.cons_cons ?_ ih
        rcases head?_insR rl x with hz | hz <;> rw [hi] at hz
        · simp at hz; subst hz; right; lia
        · cases rl with
          | nil => simp at hz
          | cons w rl =>
            simp at hz; subst hz
            have := List.rel_of_isChain_cons_cons h
            rcases this with h0 | h0
            · lia
            · right; exact h0
    · next hx =>
      refine List.IsChain.cons_cons ?_ h
      simp only [RevRel]; lia

private theorem insR_of_isChain {rl : List (Char × Nat)} {x : Char × Nat}
    (h : (x :: rl).IsChain RevRel) : insR rl x = x :: rl := by
  cases rl with
  | nil => rfl
  | cons y rl =>
    have := List.rel_of_isChain_cons_cons h
    simp only [insR, RevRel] at *
    split
    · lia
    · rfl

private theorem insR_append_starter (rl : List (Char × Nat)) {y : Char × Nat} (hy : y.2 = 0)
    (x : Char × Nat) : insR (rl ++ [y]) x = insR rl x ++ [y] := by
  induction rl with
  | nil => simp [insR, hy]
  | cons z rl ih =>
    simp only [List.cons_append, insR]
    split <;> simp [ih]

private theorem toList_reverse_of_pos {buf : Array α} (h : 0 < buf.size) :
    buf.toList.reverse = buf[buf.size - 1] :: buf.pop.toList.reverse := by
  have hne : buf.toList ≠ [] := by
    intro h'; simp [← Array.length_toList, h'] at h
  have : buf.toList = buf.pop.toList ++ [buf[buf.size - 1]] := by
    rw [Array.toList_pop]
    conv => lhs; rw [← List.dropLast_concat_getLast hne]
    simp [List.getLast_eq_getElem]
  rw [this]; simp

private theorem pushOrdered_loop (buf : Array (Char × Nat)) (x : Char × Nat) :
    (pushOrdered.loop buf x).toList.reverse = insR buf.toList.reverse x := by
  rw [pushOrdered.loop]
  split
  · next h =>
    rw [toList_reverse_of_pos h, insR]
    by_cases hc : x.2 ≠ 0 ∧ x.2 < buf[buf.size - 1].2
    · simp [hc.1, hc.2, pushOrdered_loop buf.pop x]
    · have hc' : ¬(x.2 != 0 && decide (x.2 < buf[buf.size - 1].2)) = true := by simpa using hc
      simp only [hc', hc, ite_false]
      simp only [Bool.false_eq_true, ↓reduceIte, Array.toList_push, List.reverse_append]
      rw [toList_reverse_of_pos h]; rfl
  · next h =>
    have : buf = #[] := by simp_all
    subst this; rfl
termination_by buf.size
decreasing_by simp; lia

/-- Combining class of a character, paired with it -/
private abbrev pair (c : Char) : Char × Nat := (c, getCanonicalCombiningClass c)

/-- Insert characters one by one into a buffer listed backwards -/
private def insAll (acc : List (Char × Nat)) (l : List Char) : List (Char × Nat) :=
  l.foldl (fun r c => insR r (pair c)) acc

private theorem foldl_pushOrdered (l : List Char) (buf : Array (Char × Nat)) :
    (l.foldl pushOrdered buf).toList.reverse = insAll buf.toList.reverse l := by
  induction l generalizing buf with
  | nil => rfl
  | cons c l ih => simp only [List.foldl_cons, ih, pushOrdered, pushOrdered_loop]; rfl

private theorem perm_insAll (acc : List (Char × Nat)) (l : List Char) :
    (insAll acc l).Perm ((l.map pair).reverse ++ acc) := by
  induction l generalizing acc with
  | nil => simp [insAll]
  | cons c l ih =>
    simp only [insAll, List.foldl_cons] at *
    refine (ih _).trans ?_
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact List.Perm.append_left _ (perm_insR acc (pair c))

private theorem isChain_insAll {acc : List (Char × Nat)} (h : acc.IsChain RevRel) (l : List Char) :
    (insAll acc l).IsChain RevRel := by
  induction l generalizing acc with
  | nil => exact h
  | cons c l ih => exact ih (isChain_insR h _)

private theorem isChain_of_append_right {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, (l₁ ++ l₂).IsChain R → l₂.IsChain R
  | [], _, h => h
  | _ :: _, _, h => isChain_of_append_right (List.isChain_of_isChain_cons h)

private theorem insAll_of_isChain {acc : List (Char × Nat)} {l : List Char}
    (h : ((l.map pair).reverse ++ acc).IsChain RevRel) :
    insAll acc l = (l.map pair).reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons c l ih =>
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] at *
    simp only [insAll, List.foldl_cons]
    rw [insR_of_isChain (isChain_of_append_right h)]
    exact ih h

private theorem insAll_append_starter (rl : List (Char × Nat)) {y : Char × Nat} (hy : y.2 = 0)
    (l : List Char) : insAll (rl ++ [y]) l = insAll rl l ++ [y] := by
  induction l generalizing rl with
  | nil => rfl
  | cons c l ih => simp only [insAll, List.foldl_cons] at *; rw [insR_append_starter _ hy, ih]

/-! ### Canonical order -/

private theorem isChain_cons_iff {R : α → α → Prop} {a : α} {l : List α} :
    (a :: l).IsChain R ↔ (∀ b ∈ l.head?, R a b) ∧ l.IsChain R := by
  cases l <;> simp

private theorem isChain_append_singleton_iff {R : α → α → Prop} {b : α} :
    ∀ {l : List α}, (l ++ [b]).IsChain R ↔ l.IsChain R ∧ ∀ a ∈ l.getLast?, R a b
  | [] => by simp
  | [a] => by simp
  | a :: a' :: l => by
    have := @isChain_append_singleton_iff _ R b (a' :: l)
    simp only [List.cons_append, List.isChain_cons_cons] at *
    rw [this]
    simp only [List.getLast?_cons_cons]
    exact and_assoc.symm

private theorem isChain_reverse_iff {R : α → α → Prop} :
    ∀ {l : List α}, l.reverse.IsChain R ↔ l.IsChain (fun a b => R b a)
  | [] => by simp
  | a :: l => by
    rw [List.reverse_cons, isChain_append_singleton_iff, isChain_reverse_iff, isChain_cons_iff,
      List.getLast?_reverse]
    exact and_comm

private theorem isChain_map_iff {R : β → β → Prop} {f : α → β} :
    ∀ {l : List α}, (l.map f).IsChain R ↔ l.IsChain (fun a b => R (f a) (f b))
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    have := @isChain_map_iff _ _ R f (b :: l)
    simp only [List.map_cons, List.isChain_cons_cons] at *
    rw [this]

end Normalization

/-- A list of characters is in canonical order when no nonstarter follows a character with a
  higher canonical combining class. -/
def IsCanonicallyOrdered (l : List Char) : Prop :=
  l.IsChain fun a b => getCanonicalCombiningClass b = 0 ∨
    getCanonicalCombiningClass a ≤ getCanonicalCombiningClass b

instance : DecidablePred IsCanonicallyOrdered := fun l =>
  inferInstanceAs <| Decidable <| l.IsChain fun a b => getCanonicalCombiningClass b = 0 ∨
    getCanonicalCombiningClass a ≤ getCanonicalCombiningClass b

/-- The empty list is in canonical order -/
theorem IsCanonicallyOrdered.nil : IsCanonicallyOrdered [] := List.IsChain.nil

/-- Canonical order is preserved by appending a list that starts with a starter -/
theorem isCanonicallyOrdered_append_cons {l₁ l₂ : List Char} {c : Char}
    (h₁ : IsCanonicallyOrdered l₁) (h₂ : IsCanonicallyOrdered (c :: l₂))
    (hc : getCanonicalCombiningClass c = 0) : IsCanonicallyOrdered (l₁ ++ c :: l₂) := by
  induction l₁ with
  | nil => exact h₂
  | cons a l₁ ih =>
    unfold IsCanonicallyOrdered at *
    cases l₁ with
    | nil => exact List.IsChain.cons_cons (Or.inl hc) h₂
    | cons b l₁ =>
      simp only [List.cons_append, List.isChain_cons_cons] at *
      exact ⟨h₁.1, ih h₁.2⟩

theorem IsCanonicallyOrdered.append_left {l₁ l₂ : List Char} :
    IsCanonicallyOrdered (l₁ ++ l₂) → IsCanonicallyOrdered l₁ := by
  induction l₁ with
  | nil => intro; exact IsCanonicallyOrdered.nil
  | cons a l₁ ih =>
    unfold IsCanonicallyOrdered at *
    cases l₁ with
    | nil => intro; simp
    | cons b l₁ =>
      simp only [List.cons_append, List.isChain_cons_cons] at *
      exact fun h => ⟨h.1, ih h.2⟩

theorem isCanonicallyOrdered_append_singleton_iff {l : List Char} {c : Char} :
    IsCanonicallyOrdered (l ++ [c]) ↔ IsCanonicallyOrdered l ∧ ∀ a ∈ l.getLast?,
      getCanonicalCombiningClass c = 0 ∨ getCanonicalCombiningClass a ≤ getCanonicalCombiningClass c :=
  Normalization.isChain_append_singleton_iff

namespace Normalization

/-- Pairs with correct combining classes -/
private abbrev Paired (rl : List (Char × Nat)) : Prop := ∀ x ∈ rl, x.2 = getCanonicalCombiningClass x.1

private theorem map_pair_map_fst {rl : List (Char × Nat)} (h : Paired rl) :
    (rl.map Prod.fst).map pair = rl := by
  induction rl with
  | nil => rfl
  | cons x rl ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨Prod.ext rfl (h x (by simp)).symm, ih fun y hy => h y (by simp [hy])⟩

private theorem isCanonicallyOrdered_iff_isChain (l : List Char) :
    IsCanonicallyOrdered l ↔ (l.map pair).reverse.IsChain RevRel := by
  rw [isChain_reverse_iff, isChain_map_iff]; rfl

private theorem isChain_iff_isCanonicallyOrdered {rl : List (Char × Nat)} (h : Paired rl) :
    rl.IsChain RevRel ↔ IsCanonicallyOrdered (rl.reverse.map Prod.fst) := by
  rw [isCanonicallyOrdered_iff_isChain, map_pair_map_fst (fun x hx => h x (List.mem_reverse.1 hx)),
    List.reverse_reverse]

/-! ### Decomposition -/

/-- Full decomposition of a character, with at most `n` levels of mappings -/
private def fd (compat : Bool) : Nat → Char → List Char
  | n + 1, c =>
    match getDecompositionMapping? c with
    | some ⟨tag, m⟩ => if compat || tag.isNone then m.flatMap (fd compat n) else [c]
    | none => [c]
  | 0, c => [c]

private theorem pushDecomposition_loop (compat : Bool) :
    ∀ n buf c, pushDecomposition.loop compat n buf c = (fd compat n c).foldl pushOrdered buf
  | 0, buf, c => by simp [pushDecomposition.loop, fd]
  | n + 1, buf, c => by
    simp only [pushDecomposition.loop, fd]
    rcases h : getDecompositionMapping? c with _ | ⟨tag, m⟩
    · simp
    · by_cases ht : (compat || tag.isNone) = true
      · simp only [ht, ite_true]
        rw [List.foldl_flatMap]
        congr 1; funext b a; exact pushDecomposition_loop compat n b a
      · simp_all

/-- Normalization forms without composition -/
private abbrev IsDecomposed (f : NormalizationForm) : Prop := f = .nfd ∨ f = .nfkd

/-- Characters with quick check `Y` -/
private abbrev Inert (f : NormalizationForm) (c : Char) : Prop := quickCheckChar f c = .yes

private theorem fd_of_inert {f : NormalizationForm} (hf : IsDecomposed f) {c : Char}
    (h : Inert f c) : ∀ n, fd f.isCompat n c = [c]
  | 0 => rfl
  | n + 1 => by
    rcases hf with rfl | rfl
    · simp only [Inert, quickCheckChar] at h
      simp only [fd, NormalizationForm.isCompat]
      rcases hd : getDecompositionMapping? c with _ | ⟨_ | tag, m⟩
      · rfl
      · simp [hd] at h
      · simp
    · simp only [Inert, quickCheckChar] at h
      simp only [fd, NormalizationForm.isCompat]
      rcases hd : getDecompositionMapping? c with _ | ⟨tag, m⟩
      · rfl
      · simp [hd] at h

private theorem toList_reverse_pushDecomposition (compat : Bool) (c : Char) :
    (pushDecomposition compat #[] c).toList.reverse = insAll [] (fd compat 4 c) := by
  rw [pushDecomposition, pushDecomposition_loop, foldl_pushOrdered]; rfl

private theorem inert_pushDecomposition_nfd :
    ∀ c : Char, ∀ x ∈ (pushDecomposition false #[] c).toList, Inert .nfd x.1 := by
  native_decide

private theorem inert_pushDecomposition_nfkd :
    ∀ c : Char, ∀ x ∈ (pushDecomposition true #[] c).toList, Inert .nfkd x.1 := by
  native_decide

private theorem inert_fd {f : NormalizationForm} (hf : IsDecomposed f) (c : Char) :
    ∀ d ∈ fd f.isCompat 4 c, Inert f d := by
  intro d hd
  have hm : pair d ∈ (pushDecomposition f.isCompat #[] c).toList := by
    rw [← List.mem_reverse, toList_reverse_pushDecomposition, (perm_insAll _ _).mem_iff]
    simpa using ⟨d, hd, rfl, rfl⟩
  rcases hf with rfl | rfl
  · exact inert_pushDecomposition_nfd c _ hm
  · exact inert_pushDecomposition_nfkd c _ hm

/-! ### Normalization of a whole string -/

/-- All characters have quick check `Y`, in canonical order -/
private abbrev Good (f : NormalizationForm) (l : List Char) : Prop :=
  (∀ c ∈ l, Inert f c) ∧ IsCanonicallyOrdered l

/-- Characters of `normalizeAll` -/
private def out (f : NormalizationForm) (l : List Char) : List Char :=
  (insAll [] (l.flatMap (fd f.isCompat 4))).reverse.map Prod.fst

private theorem isComposed_eq_false {f : NormalizationForm} (hf : IsDecomposed f) :
    f.isComposed = false := by
  rcases hf with rfl | rfl <;> rfl

private theorem toList_foldl_push (l : List (Char × Nat)) (t : String) :
    (l.foldl (fun s (x : Char × Nat) => match x with | (c, _) => s.push c) t).toList =
      t.toList ++ l.map Prod.fst := by
  induction l generalizing t with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem foldl_pushDecomposition (compat : Bool) (l : List Char) (buf : Array (Char × Nat)) :
    (l.foldl (pushDecomposition compat) buf).toList.reverse =
      insAll buf.toList.reverse (l.flatMap (fd compat 4)) := by
  induction l generalizing buf with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldl_cons, ih, pushDecomposition, pushDecomposition_loop, foldl_pushOrdered,
      List.flatMap_cons, insAll, insAll, insAll, List.foldl_append]

private theorem toList_normalizeAll {f : NormalizationForm} (hf : IsDecomposed f) (s : String.Slice) :
    (normalizeAll f s).toList = out f s.copy.toList := by
  simp only [normalizeAll, isComposed_eq_false hf, Bool.false_eq_true, ↓reduceIte,
    String.Slice.foldl_eq_foldl_toList, ← Array.foldl_toList]
  rw [toList_foldl_push, out]
  simp only [String.toList_empty, List.nil_append]
  rw [← List.reverse_reverse
    (Array.toList (List.foldl (pushDecomposition f.isCompat) #[] s.copy.toList)),
    foldl_pushDecomposition]
  rfl

private theorem good_out {f : NormalizationForm} (hf : IsDecomposed f) (l : List Char) :
    Good f (out f l) := by
  have hp := perm_insAll [] (l.flatMap (fd f.isCompat 4))
  have hpair : Paired (insAll [] (l.flatMap (fd f.isCompat 4))) := by
    intro x hx
    rw [hp.mem_iff] at hx
    simp only [List.append_nil, List.mem_reverse, List.mem_map] at hx
    obtain ⟨d, _, rfl⟩ := hx
    rfl
  constructor
  · intro d hd
    simp only [out, List.map_reverse, List.mem_reverse, List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    rw [hp.mem_iff] at hx
    simp only [List.append_nil, List.mem_reverse, List.mem_map, List.mem_flatMap] at hx
    obtain ⟨d, ⟨c, _, hd⟩, rfl⟩ := hx
    exact inert_fd hf c d hd
  · exact (isChain_iff_isCanonicallyOrdered hpair).1 (isChain_insAll List.IsChain.nil _)

private theorem flatMap_fd_of_good {f : NormalizationForm} (hf : IsDecomposed f) {l : List Char}
    (h : ∀ c ∈ l, Inert f c) : l.flatMap (fd f.isCompat 4) = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.flatMap_cons, fd_of_inert hf (h c (by simp)), ih fun d hd => h d (by simp [hd])]
    rfl

private theorem out_of_good {f : NormalizationForm} (hf : IsDecomposed f) {l : List Char}
    (h : Good f l) : out f l = l := by
  rw [out, flatMap_fd_of_good hf h.1,
    insAll_of_isChain (by simpa using (isCanonicallyOrdered_iff_isChain l).1 h.2)]
  simp [Function.comp_def]

private theorem out_cons_starter {f : NormalizationForm} (hf : IsDecomposed f) {c : Char}
    (l : List Char) (h0 : getCanonicalCombiningClass c = 0) (hc : Inert f c) :
    out f (c :: l) = c :: out f l := by
  rw [out, List.flatMap_cons, fd_of_inert hf hc]
  simp only [List.singleton_append, insAll, List.foldl_cons]
  have : insR [] (pair c) = [] ++ [pair c] := rfl
  rw [this]
  have := insAll_append_starter [] (y := pair c) h0 (l.flatMap (fd f.isCompat 4))
  simp only [insAll] at this
  rw [this]
  simp [out, insAll]

/-! ### Quick check -/

/-- Combining class of the last character of a list, or `0` -/
private def lastClass (l : List Char) : Nat :=
  match l.getLast? with
  | some a => getCanonicalCombiningClass a
  | none => 0

/-- `q` splits the string into a good part and a part that is empty or starts with an inert
  starter -/
private def SafeAt (f : NormalizationForm) {s : String.Slice} (q : s.Pos) : Prop :=
  ∃ t w, q.Splits t w ∧ Good f t.toList ∧
    (t = "" ∨ ∃ c r, w.toList = c :: r ∧ getCanonicalCombiningClass c = 0 ∧ Inert f c)

private theorem quickCheckChar_ne_maybe {f : NormalizationForm} (hf : IsDecomposed f) (c : Char) :
    quickCheckChar f c ≠ .maybe := by
  rcases hf with rfl | rfl <;> simp only [quickCheckChar] <;> split <;> simp

private theorem scan_loop {f : NormalizationForm} (hf : IsDecomposed f) {s : String.Slice}
    (p safe : s.Pos) (last : Nat) {t₀ u₀ : String} (hp : p.Splits t₀ u₀)
    (hg : Good f t₀.toList) (hl : last = lastClass t₀.toList) (hs : SafeAt f safe) :
    ((scan.loop f s p last .yes safe).1 = .yes ↔ Good f s.copy.toList) ∧
      ((scan.loop f s p last .yes safe).1 ≠ .yes → SafeAt f (scan.loop f s p last .yes safe).2) ∧
      (scan.loop f s p last .yes safe).1 ≠ .maybe := by
  rw [scan.loop]
  split
  · next h =>
    have hu : u₀ = "" := hp.eq_endPos_iff.1 h
    subst hu
    have : s.copy = t₀ := by simpa using hp.eq_append
    refine ⟨by simp [this]; exact hg, by simp, by simp⟩
  · next h =>
    obtain ⟨u, rfl⟩ := hp.exists_eq_singleton_append h
    have hcopy : s.copy.toList = t₀.toList ++ p.get h :: u.toList := by
      rw [hp.eq_append]; simp [String.toList_append]
    simp only
    split
    · next hc =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
      refine ⟨?_, fun _ => hs, by simp⟩
      simp only [reduceCtorEq, false_iff]
      intro hgood
      have h2 := hgood.2
      rw [hcopy, ← List.singleton_append, ← List.append_assoc] at h2
      have h3 := (isCanonicallyOrdered_append_singleton_iff.1 h2.append_left).2
      subst hl
      unfold lastClass at hc
      split at hc
      · next a ha => have := h3 a ha; lia
      · lia
    · next hc =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
      split
      · next hq =>
        refine ⟨?_, fun _ => hs, by simp⟩
        simp only [reduceCtorEq, false_iff]
        intro hgood
        have := hgood.1 (p.get h) (by simp [hcopy])
        simp [Inert, hq] at this
      · next hq => exact absurd hq (quickCheckChar_ne_maybe hf _)
      · next hq =>
        have hp' := hp.next
        have hg' : Good f (t₀ ++ String.singleton (p.get h)).toList := by
          simp only [String.toList_append, String.toList_singleton]
          refine ⟨fun c hc => ?_, ?_⟩
          · simp only [List.mem_append, List.mem_singleton] at hc
            rcases hc with hc | rfl
            · exact hg.1 c hc
            · exact hq
          · refine isCanonicallyOrdered_append_singleton_iff.2 ⟨hg.2, fun a ha => ?_⟩
            subst hl
            have ha' : t₀.toList.getLast? = some a := ha
            simp only [lastClass, ha'] at hc
            lia
        have hl' : getCanonicalCombiningClass (p.get h) =
            lastClass (t₀ ++ String.singleton (p.get h)).toList := by
          simp [lastClass]
        have hs' : SafeAt f (if (getCanonicalCombiningClass (p.get h) == 0 &&
            QuickCheck.yes == QuickCheck.yes) = true then p else safe) := by
          split
          · next h0 =>
            simp only [Bool.and_eq_true, beq_iff_eq, and_true] at h0
            exact ⟨t₀, _, hp, hg, Or.inr ⟨p.get h, u.toList, by simp [String.toList_append], h0, hq⟩⟩
          · exact hs
        exact scan_loop hf (p.next h) _ _ hp' hg' hl' hs'
termination_by p.remainingBytes
decreasing_by grind [String.Slice.Pos.lt_iff_remainingBytes_lt, String.Slice.Pos.lt_next]

private theorem scan_spec {f : NormalizationForm} (hf : IsDecomposed f) (s : String.Slice) :
    ((scan f s).1 = .yes ↔ Good f s.copy.toList) ∧ ((scan f s).1 ≠ .yes → SafeAt f (scan f s).2) ∧
      (scan f s).1 ≠ .maybe :=
  scan_loop hf s.startPos s.startPos 0 (s.splits_startPos) (by simp [Good, IsCanonicallyOrdered.nil])
    rfl ⟨"", s.copy, s.splits_startPos, by simp [Good, IsCanonicallyOrdered.nil], Or.inl rfl⟩

/-! ### Normalization -/

private theorem good_normalize {f : NormalizationForm} (hf : IsDecomposed f) (s : String.Slice) :
    Good f (normalize f s).toList := by
  obtain ⟨hy, hsafe, -⟩ := scan_spec hf s
  rcases h : scan f s with ⟨r, p⟩
  rw [h] at hy hsafe
  cases r with
  | yes => simpa [normalize, h] using hy.1 rfl
  | no | maybe =>
    obtain ⟨t, w, hp, hg, ht⟩ := hsafe (by simp)
    simp only [normalize, h, String.toList_append]
    rw [String.Slice.toString_eq, hp.copy_sliceTo_eq, toList_normalizeAll hf, hp.copy_sliceFrom_eq]
    have ho := good_out hf w.toList
    refine ⟨fun c hc => ?_, ?_⟩
    · rcases List.mem_append.1 hc with hc | hc
      · exact hg.1 c hc
      · exact ho.1 c hc
    · rcases ht with rfl | ⟨c, r, hw, h0, hc⟩
      · simpa using ho.2
      · rw [hw, out_cons_starter hf r h0 hc] at ho ⊢
        exact isCanonicallyOrdered_append_cons hg.2 ho.2 h0

private theorem normalize_of_good {f : NormalizationForm} (hf : IsDecomposed f) {s : String.Slice}
    (h : Good f s.copy.toList) : normalize f s = s.copy := by
  have hy := (scan_spec hf s).1.2 h
  rcases hs : scan f s with ⟨r, p⟩
  rw [hs] at hy
  cases hy
  simp [normalize, hs, String.Slice.toString_eq]

private theorem isNormalized_iff_good {f : NormalizationForm} (hf : IsDecomposed f)
    (s : String.Slice) : isNormalized f s ↔ Good f s.copy.toList := by
  obtain ⟨hy, -, hm⟩ := scan_spec hf s
  rcases h : scan f s with ⟨r, p⟩
  rw [h] at hy hm
  cases r with
  | yes => simpa [isNormalized, h] using hy
  | no => simpa [isNormalized, h] using hy
  | maybe => exact absurd rfl hm

private theorem inert_nfd_iff : ∀ c : Char,
    Inert .nfd c ↔ getCanonicalDecomposition c = String.singleton c := by
  native_decide

private theorem inert_nfkd_iff (c : Char) : Inert .nfkd c ↔ getDecompositionMapping? c = none := by
  cases h : getDecompositionMapping? c <;> simp [Inert, quickCheckChar, h]

end Normalization

open Normalization

/-- Normalizing an already normalized string in NFD or NFKD does nothing -/
theorem normalize_normalize {f : NormalizationForm} (hf : f = .nfd ∨ f = .nfkd)
    (s : String.Slice) : normalize f (normalize f s).toSlice = normalize f s := by
  have := Normalization.good_normalize hf s
  have := Normalization.normalize_of_good hf (s := (normalize f s).toSlice) (by simpa using this)
  simpa using this

/-- The result of normalizing to NFD or NFKD is normalized -/
theorem isNormalized_normalize {f : NormalizationForm} (hf : f = .nfd ∨ f = .nfkd)
    (s : String.Slice) : isNormalized f (normalize f s).toSlice := by
  rw [Normalization.isNormalized_iff_good hf]
  simpa using Normalization.good_normalize hf s

/-- A string is in NFD or NFKD if and only if normalizing it does nothing -/
theorem isNormalized_iff_normalize_eq {f : NormalizationForm} (hf : f = .nfd ∨ f = .nfkd)
    (s : String.Slice) : isNormalized f s ↔ normalize f s = s.copy := by
  rw [Normalization.isNormalized_iff_good hf]
  constructor
  · exact Normalization.normalize_of_good hf
  · intro h
    have := Normalization.good_normalize hf s
    rwa [h] at this

/-- Normalizing a string in NFD does nothing -/
theorem toNFD_toNFD (s : String.Slice) : toNFD (toNFD s).toSlice = toNFD s :=
  normalize_normalize (.inl rfl) s

/-- Normalizing a string in NFKD does nothing -/
theorem toNFKD_toNFKD (s : String.Slice) : toNFKD (toNFKD s).toSlice = toNFKD s :=
  normalize_normalize (.inr rfl) s

/-- The result of `toNFD` is in NFD -/
theorem isNormalized_toNFD (s : String.Slice) : isNormalized .nfd (toNFD s).toSlice :=
  isNormalized_normalize (.inl rfl) s

/-- The result of `toNFKD` is in NFKD -/
theorem isNormalized_toNFKD (s : String.Slice) : isNormalized .nfkd (toNFKD s).toSlice :=
  isNormalized_normalize (.inr rfl) s

/-- A string is in NFD if and only if no character has a canonical decomposition and the
  characters are in canonical order -/
theorem isNormalized_nfd_iff (s : String.Slice) :
    isNormalized .nfd s ↔ (∀ c ∈ s.copy.toList, getCanonicalDecomposition c = String.singleton c) ∧
      IsCanonicallyOrdered s.copy.toList := by
  rw [Normalization.isNormalized_iff_good (.inl rfl)]
  exact and_congr (forall₂_congr fun c _ => inert_nfd_iff c) Iff.rfl

/-- A string is in NFKD if and only if no character has a decomposition mapping and the
  characters are in canonical order -/
theorem isNormalized_nfkd_iff (s : String.Slice) :
    isNormalized .nfkd s ↔ (∀ c ∈ s.copy.toList, getDecompositionMapping? c = none) ∧
      IsCanonicallyOrdered s.copy.toList := by
  rw [Normalization.isNormalized_iff_good (.inr rfl)]
  exact and_congr (forall₂_congr fun c _ => inert_nfkd_iff c) Iff.rfl

/-- A string in NFKD is also in NFD -/
theorem isNormalized_nfd_of_isNormalized_nfkd {s : String.Slice} (h : isNormalized .nfkd s) :
    isNormalized .nfd s := by
  rw [isNormalized_nfkd_iff] at h
  rw [isNormalized_nfd_iff]
  refine ⟨fun c hc => ?_, h.2⟩
  have := h.1 c hc
  rw [← inert_nfd_iff]
  simp [Inert, quickCheckChar, this]

/-- A string in NFKD is unchanged by `toNFD` -/
theorem toNFD_toNFKD (s : String.Slice) : toNFD (toNFKD s).toSlice = toNFKD s := by
  have := (isNormalized_iff_normalize_eq (.inl rfl) _).1
    (isNormalized_nfd_of_isNormalized_nfkd (isNormalized_toNFKD s))
  simpa using this

end Unicode
