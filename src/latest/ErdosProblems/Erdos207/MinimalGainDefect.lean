/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MinimalForbiddenFamily
import ErdosProblems.Erdos207.ConfigurationGainDefectWitness

/-!
# The extra chosen member in a minimal-family gain defect

Non-containment is not an optional simplification: it forces every
redundant witness to expose at least one already chosen triangle outside
the tracked configuration.
-/

namespace Erdos207

open Finset

noncomputable section

theorem redundantWitness_not_subset_of_minimal
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C D : TripleSystemOn V}
    (hC : C ∈ minimalForbiddenFamily F)
    (hD : D ∈ greedyConfigurationRedundantWitnesses (minimalForbiddenFamily F) S C) :
    ¬ D ⊆ C := by
  intro hsub
  have hdata := mem_filter.mp hD
  exact hdata.2.1 (eq_of_mem_minimalForbiddenFamily_of_subset hdata.1 hC hsub)

theorem redundantWitness_outside_subset_chosen
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C D : TripleSystemOn V}
    (hD : D ∈ greedyConfigurationRedundantWitnesses F S C) :
    D \ C ⊆ S.chosen := by
  have hdata := (mem_filter.mp hD).2
  intro T hT
  have hnotA : T ∉ S.available := by
    intro hA
    exact (mem_sdiff.mp hT).2
      (mem_inter.mp (hdata.2.2.1 (mem_inter.mpr ⟨(mem_sdiff.mp hT).1, hA⟩))).1
  exact hdata.2.2.2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hT).1, hnotA⟩)

theorem redundantWitness_has_chosen_outside_of_minimal
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {C D : TripleSystemOn V}
    (hC : C ∈ minimalForbiddenFamily F)
    (hD : D ∈ greedyConfigurationRedundantWitnesses (minimalForbiddenFamily F) S C) :
    ∃ T ∈ S.chosen, T ∈ D ∧ T ∉ C := by
  obtain ⟨T, hT⟩ := sdiff_nonempty.mpr (redundantWitness_not_subset_of_minimal hC hD)
  exact ⟨T, redundantWitness_outside_subset_chosen hD hT,
    (mem_sdiff.mp hT).1, (mem_sdiff.mp hT).2⟩

end

end Erdos207
