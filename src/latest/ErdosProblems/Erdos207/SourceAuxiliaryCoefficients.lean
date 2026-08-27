/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePrefixCoefficients
import ErdosProblems.Erdos207.PreparedLocalDegreeLaw

/-! # One fixed coefficient supplies every prepared auxiliary degree bound at a prefix -/

namespace Erdos207

open Finset
open scoped NNReal

def sourceAuxiliaryCoefficient (q i : ℕ) : ℝ≥0 :=
  max 1 (sourcePrefixY q i+∑ j ∈ Icc 4 q, sourceNibbleMomentCoefficient i j 2*sourcePrefixY q i)

theorem one_le_sourceAuxiliaryCoefficient (q i : ℕ) : 1 ≤ sourceAuxiliaryCoefficient q i := le_max_left _ _

theorem sourcePrefixY_le_auxiliaryCoefficient (q i : ℕ) : sourcePrefixY q i ≤ sourceAuxiliaryCoefficient q i :=
  (le_add_of_nonneg_right zero_le).trans (le_max_right _ _)

theorem source_auxiliary_order_sum_le (q i j : ℕ) (hj : 4 ≤ j) :
    (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient i j' 2*sourcePrefixY q i) ≤
      sourceAuxiliaryCoefficient q i := by
  have hsubset : Icc j q ⊆ Icc 4 q := by
    intro j' hj'
    exact mem_Icc.mpr ⟨hj.trans (mem_Icc.mp hj').1, (mem_Icc.mp hj').2⟩
  have hsum : (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient i j' 2*sourcePrefixY q i) ≤
      ∑ j' ∈ Icc 4 q, sourceNibbleMomentCoefficient i j' 2*sourcePrefixY q i :=
    sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ zero_le)
  exact hsum.trans ((le_add_of_nonneg_left zero_le).trans (le_max_right _ _))

end Erdos207
