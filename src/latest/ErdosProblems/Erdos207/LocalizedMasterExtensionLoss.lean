/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterExtensionLoss
import ErdosProblems.Erdos207.LocalizedRootedBlocker

/-!
# Localized forbidden loss in a master transition

Every extension vertex tested at a future vortex level lies in the current
vortex set.  Consequently only forbidden completions whose missing third
vertex lies in that set can remove an extension.  This file records the
localized version of the deterministic T2--T3 loss estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Forbidden extension vertices around a rooted graph pattern, restricted
to the actual extension set. -/
def forbiddenAroundPatternIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    (Q : SimpleGraph V) (U : Finset V) : Finset V :=
  forbiddenAroundPattern F A P Q ∩ U

/-- The master extension-loss decomposition with the forbidden term
restricted to the actual extension set. -/
theorem extensionLoss_subset_support_union_removed_union_forbiddenIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U Ustar : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V}
    (hQ : Q ≤ updatedStageGraph G U M)
    (hUstar : Ustar ⊆ U)
    (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M)))
    (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F) :
    iterationExtensionVertices A Q Ustar \
        iterationExtensionVertices
          (updatedStageAvailable F U A I D M) Q Ustar ⊆
      graphSupportFinset Q ∪
        (removedAroundPattern G (updatedStageGraph G U M) Ustar Q ∪
          forbiddenAroundPatternIn F A (I ∪ (D ∪ M)) Q Ustar) := by
  intro x hx
  have hxUstar := (mem_iterationExtensionVertices_iff.mp
    (mem_sdiff.mp hx).1).1
  have hbase := extensionLoss_subset_support_union_removed_union_forbidden
    hQ hUstar htri hGleave hpacking havoid hx
  rcases mem_union.mp hbase with hsupport | hinner
  · exact mem_union_left _ hsupport
  rcases mem_union.mp hinner with hremoved | hforbidden
  · exact mem_union_right _ (mem_union_left _ hremoved)
  · exact mem_union_right _ (mem_union_right _
      (mem_inter.mpr ⟨hforbidden, hxUstar⟩))

lemma forbiddenAroundPatternIn_subset_localized_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    (Q : SimpleGraph V) (U : Finset V) :
    forbiddenAroundPatternIn F A P Q U ⊆
      (graphEdges Q).attach.biUnion fun e ↦
        (forbiddenBlockedThirdVerticesIn F A P
          (out_fst_ne_snd_of_mem_graphEdges e.2) U).image Subtype.val := by
  intro x hx
  obtain ⟨hxForbidden, hxU⟩ := mem_inter.mp hx
  unfold forbiddenAroundPattern at hxForbidden
  obtain ⟨e, heAttach, hxe⟩ := mem_biUnion.mp hxForbidden
  obtain ⟨w, hw, hwx⟩ := mem_image.mp hxe
  apply mem_biUnion.mpr
  refine ⟨e, heAttach, mem_image.mpr ⟨w, ?_, hwx⟩⟩
  exact mem_forbiddenBlockedThirdVerticesIn_iff.mpr
    ⟨hw, by simpa only [hwx] using hxU⟩

lemma card_forbiddenAroundPatternIn_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    (Q : SimpleGraph V) (U : Finset V) :
    (forbiddenAroundPatternIn F A P Q U).card ≤
      ∑ e ∈ (graphEdges Q).attach,
        (forbiddenBlockedThirdVerticesIn F A P
          (out_fst_ne_snd_of_mem_graphEdges e.2) U).card := by
  calc
    (forbiddenAroundPatternIn F A P Q U).card ≤
        ((graphEdges Q).attach.biUnion fun e ↦
          (forbiddenBlockedThirdVerticesIn F A P
            (out_fst_ne_snd_of_mem_graphEdges e.2) U).image
              Subtype.val).card :=
      card_le_card (forbiddenAroundPatternIn_subset_localized_biUnion
        F A P Q U)
    _ ≤ ∑ e ∈ (graphEdges Q).attach,
          ((forbiddenBlockedThirdVerticesIn F A P
            (out_fst_ne_snd_of_mem_graphEdges e.2) U).image
              Subtype.val).card := card_biUnion_le
    _ = ∑ e ∈ (graphEdges Q).attach,
        (forbiddenBlockedThirdVerticesIn F A P
          (out_fst_ne_snd_of_mem_graphEdges e.2) U).card := by
      apply sum_congr rfl
      intro e _he
      rw [card_image_of_injective _ Subtype.val_injective]

lemma card_forbiddenAroundPatternIn_le_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {Q : SimpleGraph V} {U : Finset V} {q r : ℕ}
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hroot : ∀ e ∈ graphEdges Q,
      (rootedActiveForbiddenConfigurationsIn
        F P e.out.1 e.out.2 U).card ≤ r) :
    (forbiddenAroundPatternIn F A P Q U).card ≤
      (graphEdges Q).card * (r * q) := by
  calc
    (forbiddenAroundPatternIn F A P Q U).card ≤
        ∑ e ∈ (graphEdges Q).attach,
          (forbiddenBlockedThirdVerticesIn F A P
            (out_fst_ne_snd_of_mem_graphEdges e.2) U).card :=
      card_forbiddenAroundPatternIn_le_sum F A P Q U
    _ ≤ ∑ _e ∈ (graphEdges Q).attach, r * q := by
      apply sum_le_sum
      intro e _he
      exact (card_forbiddenBlockedThirdVerticesIn_le_mul_rooted_activeIn
        (out_fst_ne_snd_of_mem_graphEdges e.2) U hFcard).trans
          (Nat.mul_le_mul_right q (hroot e.1 e.2))
    _ = (graphEdges Q).card * (r * q) := by simp

/-- Cardinal localized master extension-loss estimate. -/
theorem card_extensionLoss_le_of_localized_caps
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U Ustar : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V} {a r q : ℕ}
    (hQ : Q ≤ updatedStageGraph G U M)
    (hUstar : Ustar ⊆ U)
    (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M)))
    (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F)
    (hedgeCap : ∀ v ∈ graphSupportFinset Q,
      (neighborsIn G Ustar v \
        neighborsIn (updatedStageGraph G U M) Ustar v).card ≤ a)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hrootCap : ∀ e ∈ graphEdges Q,
      (rootedActiveForbiddenConfigurationsIn F (I ∪ (D ∪ M))
        e.out.1 e.out.2 Ustar).card ≤ r) :
    (iterationExtensionVertices A Q Ustar \
        iterationExtensionVertices
          (updatedStageAvailable F U A I D M) Q Ustar).card ≤
      (graphSupportFinset Q).card +
        (graphSupportFinset Q).card * a +
          (graphEdges Q).card * (r * q) := by
  have hsub := extensionLoss_subset_support_union_removed_union_forbiddenIn
    hQ hUstar htri hGleave hpacking havoid
  have hremoved :
      (removedAroundPattern G (updatedStageGraph G U M) Ustar Q).card ≤
        (graphSupportFinset Q).card * a :=
    card_removedAroundPattern_le_mul hedgeCap
  have hforbidden :
      (forbiddenAroundPatternIn F A (I ∪ (D ∪ M)) Q Ustar).card ≤
        (graphEdges Q).card * (r * q) :=
    card_forbiddenAroundPatternIn_le_mul hFcard hrootCap
  have hunionInner := (card_union_le
    (removedAroundPattern G (updatedStageGraph G U M) Ustar Q)
    (forbiddenAroundPatternIn F A (I ∪ (D ∪ M)) Q Ustar)).trans
      (Nat.add_le_add hremoved hforbidden)
  have houter := card_union_le (graphSupportFinset Q)
    (removedAroundPattern G (updatedStageGraph G U M) Ustar Q ∪
      forbiddenAroundPatternIn F A (I ∪ (D ∪ M)) Q Ustar)
  have hloss := card_le_card hsub
  omega

/-- `ℝ≥0` form used by the localized master typicality-loss event. -/
theorem extensionLoss_nnreal_le_of_localized_caps
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U Ustar : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V} {a r q : ℕ}
    {target : ℝ≥0}
    (hQ : Q ≤ updatedStageGraph G U M)
    (hUstar : Ustar ⊆ U)
    (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M)))
    (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F)
    (hedgeCap : ∀ v ∈ graphSupportFinset Q,
      (neighborsIn G Ustar v \
        neighborsIn (updatedStageGraph G U M) Ustar v).card ≤ a)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hrootCap : ∀ e ∈ graphEdges Q,
      (rootedActiveForbiddenConfigurationsIn F (I ∪ (D ∪ M))
        e.out.1 e.out.2 Ustar).card ≤ r)
    (hnumeric : ((graphSupportFinset Q).card : ℝ≥0) +
        (graphSupportFinset Q).card * a +
          (graphEdges Q).card * (r * q) ≤ target) :
    ((iterationExtensionVertices A Q Ustar \
        iterationExtensionVertices
          (updatedStageAvailable F U A I D M) Q Ustar).card : ℝ≥0) ≤
      target := by
  have hnat := card_extensionLoss_le_of_localized_caps hQ hUstar htri
    hGleave hpacking havoid hedgeCap hFcard hrootCap
  have hcast :
      ((iterationExtensionVertices A Q Ustar \
          iterationExtensionVertices
            (updatedStageAvailable F U A I D M) Q Ustar).card : ℝ≥0) ≤
        ((graphSupportFinset Q).card : ℝ≥0) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) := by
    exact_mod_cast hnat
  exact hcast.trans hnumeric

end

end Erdos207
