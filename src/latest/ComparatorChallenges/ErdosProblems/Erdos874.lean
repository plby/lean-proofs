/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos874

noncomputable def ambient (N : ℕ) : Finset ℤ :=
  Finset.Icc 1 (N : ℤ)

def restrictedSumset (r : ℕ) (A : Finset ℤ) : Finset ℤ :=
  (A.powersetCard r).image fun B => ∑ x ∈ B, x

def IsAdmissible (A : Finset ℤ) : Prop :=
  ∀ {r s : ℕ}, 0 < r → 0 < s → r ≠ s →
    Disjoint (restrictedSumset r A) (restrictedSumset s A)

open scoped Classical in
noncomputable def boundedAdmissibleFamily (N : ℕ) : Finset (Finset ℤ) :=
  (ambient N).powerset.filter IsAdmissible

noncomputable def k (N : ℕ) : ℕ :=
  (boundedAdmissibleFamily N).sup Finset.card

theorem erdos_874 :
    Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.sqrt N) atTop (nhds 2) := by
  sorry

end Erdos874
