/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

noncomputable section

namespace Erdos83

variable {N k : ℕ}

open scoped Classical in
def Uniform (k : ℕ) (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒻 → A.card = k

end Erdos83

namespace Erdos83

open scoped Classical in
def TwoIntersecting (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ ⦃A B⦄, A ∈ 𝒻 → B ∈ 𝒻 → 2 ≤ (A ∩ B).card

end Erdos83

namespace Erdos83

open scoped Classical in
theorem erdos_83 (q : ℕ) (F : Finset (Finset (Fin (4 * q))))
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F) :
    F.card ≤
      (Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2) / 2 := by
  sorry

end Erdos83

end
