/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ClosedThreatCardinality
import ErdosProblems.Erdos207.AbsorberNontrivialFamily

/-! # The threat-count estimate for the actual absorber forbidden family -/

namespace Erdos207

open Finset

noncomputable section

theorem card_add_two_le_of_mem_absorberErdosForbidden
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {B C : TripleSystemOn V}
    (hC : C ∈ absorberErdosForbiddenConfigurationsOn q B) : C.card + 2 ≤ q := by
  obtain ⟨_, r, hr4, hrq, E, hE, _, hEC⟩ := mem_absorberErdosForbiddenConfigurationsOn_iff.mp hC
  have hsub : C ⊆ E := by rw [← hEC]; exact sdiff_subset
  have hc := card_le_card hsub
  have he := hE.1.1
  omega

theorem abs_absorberClosedThreats_sub_terminal_sum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    {q : ℕ} {B : TripleSystemOn V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    |((greedyClosedThreats F S T).card : ℝ) -
      ((∑ P ∈ T.1.powersetCard 2, ((availableTrianglesContainingPair S P).card : ℝ)) +
        (∑ j ∈ Icc 4 q, ((greedyConfigurationClass
          (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ)) - 2)| ≤
      (selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen : ℝ) := by
  exact abs_closedThreats_sub_terminal_sum_le hS hT
    (fun E hE ↦ isPacking_of_mem_absorberErdosForbidden (hF hE))
    (fun E hE _ ↦ card_add_two_le_of_mem_absorberErdosForbidden (hF hE))

end

end Erdos207
