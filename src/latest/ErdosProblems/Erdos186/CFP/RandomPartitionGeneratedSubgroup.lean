/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomPartitionSharp
import ErdosProblems.Erdos186.CFP.RandomGreedyDenseWitness

/-!
# Generated subgroup of an anchored color class

This file connects the anchored color classes used by the sharp random
partition theorem with the unanchored integer color classes consumed by the
greedy-completion construction.  The only additional point is zero, whose
image contributes nothing to the generated subgroup.
-/

namespace Erdos186.CFP.RandomPartition

noncomputable section

set_option autoImplicit false

/-- Adding the common zero anchor to an integer color class does not change
its generated coordinate subgroup when the coordinate map sends zero to
zero. -/
theorem generatedSubgroup_integerColorClass_eq_anchoredColorClass
    {A : Finset ℤ} {q d : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (i : Fin (q + 1))
    (φ : ℤ → LatticePoint d) (hφ0 : φ 0 = 0) :
    Stability.generatedSubgroup φ (integerColorClass A c i) =
      Stability.generatedSubgroup φ (anchoredColorClass A c i) := by
  apply le_antisymm
  · apply Stability.generatedSubgroup_mono
    exact Finset.subset_insert 0 (integerColorClass A c i)
  · rw [Stability.generatedSubgroup, AddSubgroup.closure_le]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [anchoredColorClass] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · rw [hφ0]
      exact AddSubgroup.zero_mem _
    · exact AddSubgroup.subset_closure ⟨z, hz, rfl⟩

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.generatedSubgroup_integerColorClass_eq_anchoredColorClass
