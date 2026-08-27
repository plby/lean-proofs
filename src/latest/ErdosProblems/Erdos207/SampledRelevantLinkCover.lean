/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousRobustLinkCover

/-! # Robust Hall with deletion degrees restricted to actual sampled candidates -/

namespace Erdos207

open Finset

noncomputable section

def sampledCandidatePairs
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (R : Finset (A × B)) : Finset (A × B) :=
  R.filter fun ab ↦ r ab.1 ab.2

theorem IsTwoSidedRobustMatchingSample.sampled_candidates
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {r : A → B → Prop} [DecidableRel r] {Delta : ℕ} {R : Finset (A × B)}
    (h : IsTwoSidedRobustMatchingSample r Delta R) :
    IsTwoSidedRobustMatchingSample (fun a b ↦ (a, b) ∈ sampledCandidatePairs r R) Delta
      (sampledCandidatePairs r R) := by
  intro deleted _ hleft hright
  obtain ⟨f, hf, hmatch⟩ := h deleted hleft hright
  refine ⟨f, hf, ?_⟩
  intro a
  have hm : (a, f a) ∈ sampledCandidatePairs r R := mem_filter.mpr ⟨(hmatch a).2.1, (hmatch a).1⟩
  exact ⟨hm, hm, (hmatch a).2.2⟩

theorem exists_reservoirLinkCover_of_sampled_candidate_bad_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V) (K : BipartiteLink V)
    (r : ↥K.left → ↥K.right → Prop) [DecidableRel r]
    (Delta : ℕ) (R : Finset (↥K.left × ↥K.right))
    (hrobust : IsTwoSidedRobustMatchingSample r Delta R)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ a b, r a b → (a, b) ∈ R →
      linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b ∈ available)
    (hleftBad : ∀ a, (deletedNeighbors
      (bipartiteLinkRelevantBadPair (fun a b ↦ (a, b) ∈ sampledCandidatePairs r R)
        F P (sampledCandidatePairs r R)) a).card ≤ Delta)
    (hrightBad : ∀ b, (deletedNeighbors (transposeRelation
      (bipartiteLinkRelevantBadPair (fun a b ↦ (a, b) ∈ sampledCandidatePairs r R)
        F P (sampledCandidatePairs r R))) b).card ≤ Delta) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ M ⊆ bipartiteLinkReservoir K R ∧ Disjoint P M ∧
        IsPackingOn (P ∪ M) ∧ AvoidsForbidden (P ∪ M) F ∧ CoversBipartiteLink K M := by
  obtain ⟨M, hMa, hMR, hdis, hpack, havoid, hcover⟩ :=
    exists_reservoirLinkCover_of_twoSidedRobustSample F available P K
      (fun a b ↦ (a, b) ∈ sampledCandidatePairs r R) Delta (sampledCandidatePairs r R)
      hrobust.sampled_candidates hPpacking hPavoid
      (fun a b hab _ ↦ havailable a b (mem_filter.mp hab).2 (mem_filter.mp hab).1) hleftBad hrightBad
  refine ⟨M, hMa, ?_, hdis, hpack, havoid, hcover⟩
  apply hMR.trans
  exact image_subset_image (filter_subset _ _)

end

end Erdos207
