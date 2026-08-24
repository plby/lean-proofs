import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.AddTorsor

namespace Theorem61

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

theorem ceva_theorem
    (b : AffineBasis (Fin 3) ℝ P)
    (A₁ B₁ C₁ : P)
    (hA₁ : A₁ ∈ affineSegment ℝ (b 1) (b 2))
    (hB₁ : B₁ ∈ affineSegment ℝ (b 2) (b 0))
    (hC₁ : C₁ ∈ affineSegment ℝ (b 0) (b 1))
    (hA₁_ne_B : A₁ ≠ b 1) (hA₁_ne_C : A₁ ≠ b 2)
    (hB₁_ne_C : B₁ ≠ b 2) (hB₁_ne_A : B₁ ≠ b 0)
    (hC₁_ne_A : C₁ ≠ b 0) (hC₁_ne_B : C₁ ≠ b 1) :
    (∃ O : P,
      O ∈ line[ℝ, b 0, A₁] ∧ O ∈ line[ℝ, b 1, B₁] ∧
        O ∈ line[ℝ, b 2, C₁]) ↔
    dist (b 1) A₁ * dist (b 2) B₁ * dist (b 0) C₁ =
      dist A₁ (b 2) * dist B₁ (b 0) * dist C₁ (b 1) := by
  sorry

end Theorem61
