/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped BigOperators Pointwise Topology
open Function

noncomputable section


namespace Erdos748

open scoped Classical in
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ ⦃b c : ℕ⦄, b ∈ A → c ∈ A → b + c ∉ A

end Erdos748

namespace Erdos748

open scoped Classical in
def sumFreeSubsets (n : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 n).powerset.filter IsSumFree

end Erdos748

namespace Erdos748

open scoped Classical in
def sumFreeCount (n : ℕ) : ℕ :=
  (sumFreeSubsets n).card

end Erdos748

namespace Erdos748

open scoped Classical in
theorem erdos_748 :
    Tendsto (fun n : ℕ ↦ Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ)) atTop
      (𝓝 (1 / 2 : ℝ)) := by
  sorry

end Erdos748

end
