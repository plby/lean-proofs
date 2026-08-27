/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRootPerturbation
import ErdosProblems.Erdos207.InitialResidualPairs
import ErdosProblems.Erdos207.KSSSConfigurationPowerDrift
import ErdosProblems.Erdos207.AbsorberClosedThreatCount

/-! # Exact dynamics and avoidance for the restricted initial family -/

namespace Erdos207

open Finset

noncomputable section

theorem GreedyInvariant.forbidden_subset
    {V : Type*} [DecidableEq V] {F G : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hS : GreedyInvariant F S) (hGF : G ⊆ F) : GreedyInvariant G S := by
  refine ⟨hS.1, fun C hC ↦ hS.2.1 C (hGF hC), ?_⟩
  intro T hT
  have ht := hS.2.2 T hT
  exact ⟨ht.1, ht.2.1, fun C hC ↦ ht.2.2 C (hGF hC)⟩

theorem initialRestrictedAbsorberFamily_data
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (bank ambient : TripleSystemOn V) :
    let F := initialRestrictedAbsorberFamily q bank ambient
    minimalForbiddenFamily F = F ∧
      F ⊆ absorberErdosForbiddenConfigurationsOn q bank ∧
      (∀ C ∈ F, C ⊆ ambient) ∧
      (∀ C ∈ F, IsPackingOn C) ∧ (∀ C ∈ F, C.card + 2 ≤ q) := by
  dsimp only
  have hsub : initialRestrictedAbsorberFamily q bank ambient ⊆
      absorberErdosForbiddenConfigurationsOn q bank := fun _ hC ↦ (mem_minimal_restrict_subset hC).1
  exact ⟨minimalForbiddenFamily_idempotent _, hsub,
    fun _ hC ↦ (mem_minimal_restrict_subset hC).2,
    fun _ hC ↦ isPacking_of_mem_absorberErdosForbidden (hsub hC),
    fun _ hC ↦ card_add_two_le_of_mem_absorberErdosForbidden (hsub hC)⟩

theorem initialRestrictedAbsorberFamily_initial_invariant
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V) :
    let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
      (outsideAvailableTriangles H bank)
    GreedyInvariant (initialRestrictedAbsorberFamily q bank S.available) S := by
  dsimp only
  exact (absorberGreedyInitialState_invariant _ _ (fun _ hC ↦ absorberErdosForbidden_nonempty hC)).1.forbidden_subset
    (initialRestrictedAbsorberFamily_data q bank _).2.1

theorem initialRestrictedAbsorberFamily_restore_invariant
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (bank ambient : TripleSystemOn V)
    (S : GreedyStateOn V) (hS : GreedyInvariant (initialRestrictedAbsorberFamily q bank ambient) S)
    (hcontained : GreedyContainedIn ambient S) :
    GreedyInvariant (absorberErdosForbiddenConfigurationsOn q bank) S := by
  refine ⟨hS.1, (avoidsForbidden_minimal_restrict_iff _ _ _ hcontained.1).mp hS.2.1, ?_⟩
  intro T hT
  have ht := hS.2.2 T hT
  exact ⟨ht.1, ht.2.1, (avoidsForbidden_minimal_restrict_iff _ _ _
    (insert_subset_iff.mpr ⟨hcontained.2 hT, hcontained.1⟩)).mp ht.2.2⟩

theorem initialResidualPairs_cover_all_triangle_pairs
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V)
    {T : TripleOn V} (hT : T ∈ (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)).available)
    {Q : Finset V} (hQ : Q.card = 2) (hQT : Q ⊆ T.1) : Q ∈ initialResidualPairs H :=
  initialResidualPairs_cover_available q H bank hQ
    ⟨T, mem_availableTrianglesContainingPair_iff.mpr ⟨hT, hQT⟩⟩

end

end Erdos207
