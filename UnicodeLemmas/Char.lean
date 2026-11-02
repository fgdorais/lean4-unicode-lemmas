/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

namespace Char

/-- Decide a property of all characters by checking each one. -/
instance decidableForall (p : Char → Prop) [DecidablePred p] : Decidable (∀ c, p c) :=
  decidable_of_iff (∀ f : Fin Char.numCodePoints, p (Char.ofOrdinal f)) <| by
    constructor
    · intro h c; simpa using h c.ordinal
    · intro h f; exact h _

/-- Decide whether some character has a property by checking each one. -/
instance decidableExists (p : Char → Prop) [DecidablePred p] : Decidable (∃ c, p c) :=
  decidable_of_iff (∃ f : Fin Char.numCodePoints, p (Char.ofOrdinal f)) <| by
    constructor
    · intro ⟨f, h⟩; exact ⟨_, h⟩
    · intro ⟨c, h⟩; exact ⟨c.ordinal, by simpa using h⟩

end Char
