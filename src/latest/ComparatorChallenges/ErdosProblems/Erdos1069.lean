/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Classical
open scoped Real

noncomputable section


open scoped Classical in
def IsAffineLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1

namespace Erdos1069

open scoped Classical in
abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos1069

namespace Erdos1069

open scoped Classical in
abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

end Erdos1069

namespace Erdos1069

open scoped Classical in
noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ : AffineSubspace ℝ Point)).card

end Erdos1069

namespace Erdos1069

open scoped Classical in
theorem erdos_1069 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset Point) (k : ℕ),
        2 ≤ k → (k : ℝ) ≤ Real.sqrt (P.card : ℝ) →
          ∃ L : Finset Line,
            (∀ ℓ, ℓ ∈ L ↔ k ≤ richness P ℓ) ∧
            (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
  sorry

end Erdos1069

end
