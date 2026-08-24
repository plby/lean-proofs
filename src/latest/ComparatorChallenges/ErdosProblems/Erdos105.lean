/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos105

abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

noncomputable def lineThrough (p q : R2) : AffineSubspace ℝ R2 :=
  affineSpan ℝ ({p, q} : Set R2)

def IsLine (ℓ : AffineSubspace ℝ R2) : Prop :=
  ∃ p q : R2, p ≠ q ∧ ℓ = lineThrough p q

end Erdos105

theorem Erdos105.not_erdos_105 :
    Not (∀ (A B : Finset Erdos105.R2) (n : ℕ),
    Disjoint A B →
    A.card = n →
    B.card = n - 3 →
    (¬ ∃ ℓ : AffineSubspace ℝ Erdos105.R2, Erdos105.IsLine ℓ ∧ (A : Set Erdos105.R2) ⊆ (ℓ : Set Erdos105.R2)) →
    ∃ (p q : Erdos105.R2),
      p ∈ A ∧ q ∈ A ∧ p ≠ q ∧
      (∀ b ∈ B, b ∉ (Erdos105.lineThrough p q : Set Erdos105.R2))) := by
  sorry
