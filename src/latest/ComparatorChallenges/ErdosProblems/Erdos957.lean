/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

noncomputable section


namespace Erdos957

open scoped Classical in
abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos957

namespace Erdos957

open scoped Classical in
noncomputable def distanceSet (A : Finset Point) : Finset ℝ := by
  classical
  exact ((A.product A).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ dist p.1 p.2

end Erdos957

namespace Erdos957

open scoped Classical in
def IsMinimumDistance (A : Finset Point) (r : ℝ) : Prop :=
  r ∈ distanceSet A ∧ ∀ s ∈ distanceSet A, r ≤ s

end Erdos957

namespace Erdos957

open scoped Classical in
def IsMaximumDistance (A : Finset Point) (r : ℝ) : Prop :=
  r ∈ distanceSet A ∧ ∀ s ∈ distanceSet A, s ≤ r

end Erdos957

namespace Erdos957

open scoped Classical in
noncomputable def distanceGraph (A : Finset Point) (r : ℝ) :
    SimpleGraph {x // x ∈ A} where
  Adj x y := x ≠ y ∧ dist (x : Point) (y : Point) = r
  symm.symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa [dist_comm] using h.2⟩
  loopless.irrefl := by
    intro x h
    exact h.1 rfl

end Erdos957

namespace Erdos957

open scoped Classical in
noncomputable instance distanceGraph.instDecidableRelAdj
    (A : Finset Point) (r : ℝ) : DecidableRel (distanceGraph A r).Adj :=
  Classical.decRel _

end Erdos957

namespace Erdos957

open scoped Classical in
noncomputable def multiplicity (A : Finset Point) (r : ℝ) : ℕ :=
  (distanceGraph A r).edgeFinset.card

end Erdos957

namespace Erdos957

open scoped Classical in
def HasLinearErrorBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : Finset Point) (d₁ dₖ : ℝ),
      IsMinimumDistance A d₁ →
      IsMaximumDistance A dₖ →
      (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
        (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + C * A.card

end Erdos957

namespace Erdos957

open scoped Classical in
theorem erdos957 : HasLinearErrorBound := by
  sorry

end Erdos957

end
