/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

noncomputable section

namespace Erdos874

open scoped Classical in
def ambient (N : ℕ) : Finset ℤ :=
  Finset.Icc 1 (N : ℤ)

end Erdos874

namespace Erdos874

open scoped Classical in
def restrictedSumset (r : ℕ) (A : Finset ℤ) : Finset ℤ :=
  (A.powersetCard r).image fun B => ∑ x ∈ B, x

end Erdos874

namespace Erdos874

open scoped Classical in
def IsAdmissible (A : Finset ℤ) : Prop :=
  ∀ {r s : ℕ}, 0 < r → 0 < s → r ≠ s →
    Disjoint (restrictedSumset r A) (restrictedSumset s A)

end Erdos874

namespace Erdos874

open scoped Classical in
noncomputable def boundedAdmissibleFamily (N : ℕ) : Finset (Finset ℤ) :=
  (ambient N).powerset.filter IsAdmissible

end Erdos874

namespace Erdos874

open scoped Classical in
noncomputable def k (N : ℕ) : ℕ :=
  (boundedAdmissibleFamily N).sup Finset.card

end Erdos874

namespace Erdos874

open scoped Classical in
theorem erdos_874 :
    Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.sqrt N) atTop (nhds 2) := by
  sorry

end Erdos874

end
