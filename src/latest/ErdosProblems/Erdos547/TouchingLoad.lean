import ErdosProblems.Erdos547.AllocationRestriction

/-!
# Retaining incident edges preserves the load on the selected set
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

theorem SkewMatching.touching_load_of_mem (σ : SkewMatching G γ) {C : Set V}
    {u : V} (hu : u ∈ C) : (σ.touching C).load u = σ.load u := by
  have hout (v : V) := σ.touching_weight_of_mem (Or.inl hu : u ∈ C ∨ v ∈ C)
  have hin (v : V) := σ.touching_weight_of_mem (Or.inr hu : v ∈ C ∨ u ∈ C)
  simp only [SkewMatching.load, SkewMatching.outLoad, SkewMatching.inLoad, hout, hin]

theorem FractionalMatching.touching_load_of_mem (ν : FractionalMatching G) {C : Set V}
    {u : V} (hu : u ∈ C) : (ν.touching C).load u = ν.load u := by
  exact Finset.sum_congr rfl fun v _ ↦ ν.touching_weight_of_mem (Or.inl hu)

theorem FractionalMatching.touching_weight_le (ν : FractionalMatching G) (C : Set V)
    (u v : V) : (ν.touching C).weight u v ≤ ν.weight u v := by
  classical
  by_cases h : u ∈ C ∨ v ∈ C
  · rw [ν.touching_weight_of_mem h]
  · rw [ν.touching_weight_of_notMem (not_or.mp h).1 (not_or.mp h).2]
    exact ν.nonnegative u v

end Erdos547.DPRS
