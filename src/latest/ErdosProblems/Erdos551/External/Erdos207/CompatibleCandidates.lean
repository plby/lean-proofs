/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.ForbiddenCompletionCount

/-!
# Packing-compatible third vertices

Near the end of a cover-down stage, total covered degrees are large, so the
useful extension supply is not estimated by subtracting those degrees.  It is
the common leave-neighborhood of the endpoints, intersected with ambient
availability.  This file gives the exact finite formulation used by the KSSS
typicality estimates.
-/

namespace Erdos207

open Finset

/-- Ambient candidates whose two new pairs are still uncovered. -/
noncomputable def packingCompatibleThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (A P : TripleSystemOn V) {u v : V} (huv : u ≠ v) :
    Finset (ThirdVertex u v) := by
  classical
  exact (candidateThirdVertices A huv).filter fun w ↦
    TriangleAvoidsGraph (coveredGraph P) (thirdVertexTriple huv w)

@[simp]
lemma mem_packingCompatibleThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V} {huv : u ≠ v}
    {w : ThirdVertex u v} :
    w ∈ packingCompatibleThirdVertices A P huv ↔
      thirdVertexTriple huv w ∈ A ∧
        TriangleAvoidsGraph (coveredGraph P) (thirdVertexTriple huv w) := by
  classical
  simp [packingCompatibleThirdVertices, mem_candidateThirdVertices_iff]

/-- On an uncovered root pair, compatibility is exactly membership of the
third vertex in both leave neighborhoods. -/
lemma mem_packingCompatibleThirdVertices_iff_leave
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V}
    (huv : (leaveGraph P).Adj u v) {w : ThirdVertex u v} :
    w ∈ packingCompatibleThirdVertices A P huv.ne ↔
      thirdVertexTriple huv.ne w ∈ A ∧
        (leaveGraph P).Adj u w.1 ∧ (leaveGraph P).Adj v w.1 := by
  rw [mem_packingCompatibleThirdVertices_iff,
    triangleAvoidsGraph_thirdVertexTriple_iff]
  simp only [leaveGraph_adj]
  constructor
  · rintro ⟨hA, _huvUncovered, huwUncovered, hvwUncovered⟩
    exact ⟨hA, ⟨w.2.1.symm, huwUncovered⟩,
      ⟨w.2.2.symm, hvwUncovered⟩⟩
  · rintro ⟨hA, ⟨_huw, huwUncovered⟩, ⟨_hvw, hvwUncovered⟩⟩
    exact ⟨hA, huv.2, huwUncovered, hvwUncovered⟩

/-- A surplus of packing-compatible candidates over forbidden threats gives
a legal triangle through the uncovered pair. -/
theorem legalThirdVertices_nonempty_of_forbidden_lt_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    {u v : V} (huv : (leaveGraph P).Adj u v)
    (hcount :
      (forbiddenBlockedThirdVertices F A P huv.ne).card <
        (packingCompatibleThirdVertices A P huv.ne).card) :
    (legalThirdVertices F A P huv.ne).Nonempty := by
  have hex : ∃ w ∈ packingCompatibleThirdVertices A P huv.ne,
      w ∉ forbiddenBlockedThirdVertices F A P huv.ne := by
    by_contra hnone
    push Not at hnone
    have hsub : packingCompatibleThirdVertices A P huv.ne ⊆
        forbiddenBlockedThirdVertices F A P huv.ne := by
      intro w hw
      exact hnone w hw
    exact (Nat.not_lt_of_ge (card_le_card hsub)) hcount
  obtain ⟨w, hwCompatible, hwForbidden⟩ := hex
  obtain ⟨hTA, havoids⟩ :=
    mem_packingCompatibleThirdVertices_iff.mp hwCompatible
  have hTnotP : thirdVertexTriple huv.ne w ∉ P := by
    intro hTP
    exact huv.2 (coveredGraph_adj.mp (coveredGraph_adj.mpr
      ⟨thirdVertexTriple huv.ne w, hTP,
        left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
        huv.ne⟩))
  have hnotCompletes :
      ¬CompletesForbidden F P (thirdVertexTriple huv.ne w) := by
    intro hcomplete
    exact hwForbidden
      (mem_forbiddenBlockedThirdVertices_iff.mpr ⟨hTA, hcomplete⟩)
  refine ⟨w, mem_legalThirdVertices_iff.mpr ⟨hTA, ?_⟩⟩
  exact (isLegalExtension_iff hpacking havoid _).mpr
    ⟨hTnotP, havoids, hnotCompletes⟩

theorem outsideLeaveEdgesLegallyExtendable_of_forbidden_lt_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {H : SimpleGraph V} {X : Finset V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (forbiddenBlockedThirdVertices F A P huv.1.ne).card <
        (packingCompatibleThirdVertices A P huv.1.ne).card) :
    OutsideLeaveEdgesLegallyExtendable F A P H X := by
  intro u v huv houtside
  obtain ⟨w, hw⟩ := legalThirdVertices_nonempty_of_forbidden_lt_compatible
    hpacking havoid huv.1 (hcount huv houtside)
  have hw' := mem_legalThirdVertices_iff.mp hw
  exact ⟨thirdVertexTriple huv.1.ne w, hw'.1,
    left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _, hw'.2⟩

/-- Rooted active configurations are the sole forbidden loss in the useful
common-leave supply criterion. -/
theorem graphSupportedOn_of_maximal_absorber_rooted_lt_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P : TripleSystemOn V}
    (hpacking : IsPackingOn P)
    (havoid : AvoidsForbidden P
      (absorberErdosForbiddenConfigurationsOn q B))
    (hmax : legalAvailable
      (absorberErdosForbiddenConfigurationsOn q B) P
      (outsideAvailableTriangles H B) = ∅)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B) P u v).card * q <
        (packingCompatibleThirdVertices
          (outsideAvailableTriangles H B) P huv.1.ne).card) :
    GraphSupportedOn (graphDifference (leaveGraph P) H) (X : Set V) := by
  apply graphSupportedOn_of_maximal_legal hmax
  apply outsideLeaveEdgesLegallyExtendable_of_forbidden_lt_compatible
    hpacking havoid
  intro u v huv houtside
  have hforbidden :=
    card_forbiddenBlockedThirdVertices_le_mul_rooted_active
      (F := absorberErdosForbiddenConfigurationsOn q B)
      (A := outsideAvailableTriangles H B) (P := P) huv.1.ne
      (fun S hS ↦ card_le_cutoff_of_mem_absorberErdosForbidden hS)
  exact hforbidden.trans_lt (hcount huv houtside)

end Erdos207
