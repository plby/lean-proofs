import Mathlib

open Classical
open scoped Real

noncomputable section

attribute [local instance] Classical.propDecidable

def IsAffineLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1

namespace Erdos1069

abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos1069

namespace Erdos1069

abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

end Erdos1069

namespace Erdos1069

noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ : AffineSubspace ℝ Point)).card

end Erdos1069

namespace Erdos1069

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
