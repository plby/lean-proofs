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

def erdos_105 : Prop :=
  ∀ (A B : Finset R2) (n : ℕ),
  Disjoint A B →
  A.card = n →
  B.card = n - 3 →
  (¬ ∃ ℓ : AffineSubspace ℝ R2, IsLine ℓ ∧ (A : Set R2) ⊆ (ℓ : Set R2)) →
  ∃ (p q : R2),
    p ∈ A ∧ q ∈ A ∧ p ≠ q ∧
    (∀ b ∈ B, b ∉ (lineThrough p q : Set R2))
end Erdos105

open scoped Classical in
theorem Erdos105.not_erdos_105 :
    Not Erdos105.erdos_105
  := by
  sorry
