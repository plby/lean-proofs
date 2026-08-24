/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace Erdos748

def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ ⦃b c : ℕ⦄, b ∈ A → c ∈ A → b + c ∉ A

noncomputable def sumFreeSubsets (n : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 n).powerset.filter IsSumFree

noncomputable def sumFreeCount (n : ℕ) : ℕ :=
  (sumFreeSubsets n).card

theorem erdos_748 :
    Tendsto (fun n : ℕ ↦ Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ)) atTop
      (𝓝 (1 / 2 : ℝ)) := by
  sorry

end Erdos748
