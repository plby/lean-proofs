/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledRelevantLinkCover
import ErdosProblems.Erdos207.SourceLinkSampledForbiddenCount

/-! # Both sampled link orientations inject into the forbidden-triangle count -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sampledLinkForbiddenPair
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) (b : ↥K.right) : Prop :=
  (a, b) ∈ R ∧ ParticipatesForbidden F P (bipartiteLinkReservoir K R)
    (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
      K.center_ne_left K.center_ne_right K.left_ne_right a b)

theorem sampledLinkForbiddenPair_left_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (I D P Q : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (hP : P ⊆ I ∪ D ∪ Q) (hR : bipartiteLinkReservoir K R ⊆ Q) (a : ↥K.left) :
    (deletedNeighbors (sampledLinkForbiddenPair F P K R) a).card ≤
      (sourceLinkForbiddenSamples F I D Q s(K.center, K.leftEmbedding a)).card := by
  let encode := linkPairTripleEmbedding K.center K.leftEmbedding K.rightEmbedding
    K.center_ne_left K.center_ne_right K.left_ne_right
  apply card_le_card_of_injOn (f := fun b : ↥K.right ↦ encode (a, b))
  · intro b hb
    have hm : sampledLinkForbiddenPair F P K R a b :=
      (mem_deletedNeighbors_iff (sampledLinkForbiddenPair F P K R)).mp hb
    obtain ⟨E, hE, hTE, hEP⟩ := hm.2
    apply mem_filter.mpr
    refine ⟨hR (mem_image.mpr ⟨(a, b), hm.1, rfl⟩), ?_, E, hE, hTE, ?_⟩
    · exact mk_mem_tripleEdgeFinset_iff.mpr
        ⟨by change K.center ∈ ({K.center, K.leftEmbedding a, K.rightEmbedding b} : Finset V); simp,
          by change K.leftEmbedding a ∈ ({K.center, K.leftEmbedding a, K.rightEmbedding b} : Finset V); simp,
          K.center_ne_left a⟩
    · exact hEP.trans (union_subset hP (hR.trans subset_union_right))
  · intro b _ c _ hbc
    have hpairs : (a, b) = (a, c) := encode.injective hbc
    exact congrArg (fun p : ↥K.left × ↥K.right ↦ p.2) hpairs

theorem sampledLinkForbiddenPair_right_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (I D P Q : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (hP : P ⊆ I ∪ D ∪ Q) (hR : bipartiteLinkReservoir K R ⊆ Q) (b : ↥K.right) :
    (deletedNeighbors (transposeRelation (sampledLinkForbiddenPair F P K R)) b).card ≤
      (sourceLinkForbiddenSamples F I D Q s(K.center, K.rightEmbedding b)).card := by
  let encode := linkPairTripleEmbedding K.center K.leftEmbedding K.rightEmbedding
    K.center_ne_left K.center_ne_right K.left_ne_right
  apply card_le_card_of_injOn (f := fun a : ↥K.left ↦ encode (a, b))
  · intro a ha
    have hm : sampledLinkForbiddenPair F P K R a b :=
      (mem_deletedNeighbors_iff (transposeRelation (sampledLinkForbiddenPair F P K R))).mp ha
    obtain ⟨E, hE, hTE, hEP⟩ := hm.2
    apply mem_filter.mpr
    refine ⟨hR (mem_image.mpr ⟨(a, b), hm.1, rfl⟩), ?_, E, hE, hTE, ?_⟩
    · exact mk_mem_tripleEdgeFinset_iff.mpr
        ⟨by change K.center ∈ ({K.center, K.leftEmbedding a, K.rightEmbedding b} : Finset V); simp,
          by change K.rightEmbedding b ∈ ({K.center, K.leftEmbedding a, K.rightEmbedding b} : Finset V); simp,
          K.center_ne_right b⟩
    · exact hEP.trans (union_subset hP (hR.trans subset_union_right))
  · intro a _ c _ hac
    have hpairs : (a, b) = (c, b) := encode.injective hac
    exact congrArg (fun p : ↥K.left × ↥K.right ↦ p.1) hpairs

theorem sampledLinkBadPair_left_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (I D P Q : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (hP : P ⊆ I ∪ D ∪ Q) (hR : bipartiteLinkReservoir K R ⊆ Q) (a : ↥K.left) :
    (deletedNeighbors (bipartiteLinkRelevantBadPair (fun a b ↦ (a, b) ∈ R) F P R) a).card ≤
      (bipartiteLinkRelevantPairConflictNeighbors (fun a b ↦ (a, b) ∈ R) P a).card +
        (sourceLinkForbiddenSamples F I D Q s(K.center, K.leftEmbedding a)).card := by
  have hsub : deletedNeighbors (bipartiteLinkRelevantBadPair (fun a b ↦ (a, b) ∈ R) F P R) a ⊆
      bipartiteLinkRelevantPairConflictNeighbors (fun a b ↦ (a, b) ∈ R) P a ∪
        deletedNeighbors (sampledLinkForbiddenPair F P K R) a := by
    intro b hb
    rw [mem_deletedNeighbors_iff] at hb
    obtain ⟨hr, hconflict | hforbidden⟩ := hb
    · apply mem_union_left
      simpa only [bipartiteLinkRelevantPairConflictNeighbors, mem_filter, mem_univ, true_and] using And.intro hr hconflict
    · apply mem_union_right
      rw [mem_deletedNeighbors_iff]
      exact ⟨hr, hforbidden⟩
  exact ((card_le_card hsub).trans (card_union_le _ _)).trans
    (Nat.add_le_add_left (sampledLinkForbiddenPair_left_card_le F I D P Q K R hP hR a) _)

theorem sampledLinkBadPair_right_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (I D P Q : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (hP : P ⊆ I ∪ D ∪ Q) (hR : bipartiteLinkReservoir K R ⊆ Q) (b : ↥K.right) :
    (deletedNeighbors (transposeRelation
      (bipartiteLinkRelevantBadPair (fun a b ↦ (a, b) ∈ R) F P R)) b).card ≤
      (bipartiteLinkRelevantRightPairConflictNeighbors (fun a b ↦ (a, b) ∈ R) P b).card +
        (sourceLinkForbiddenSamples F I D Q s(K.center, K.rightEmbedding b)).card := by
  have hsub : deletedNeighbors (transposeRelation
      (bipartiteLinkRelevantBadPair (fun a b ↦ (a, b) ∈ R) F P R)) b ⊆
      bipartiteLinkRelevantRightPairConflictNeighbors (fun a b ↦ (a, b) ∈ R) P b ∪
        deletedNeighbors (transposeRelation (sampledLinkForbiddenPair F P K R)) b := by
    intro a ha
    rw [mem_deletedNeighbors_iff] at ha
    obtain ⟨hr, hconflict | hforbidden⟩ := ha
    · apply mem_union_left
      simpa only [bipartiteLinkRelevantRightPairConflictNeighbors, mem_filter, mem_univ, true_and] using And.intro hr hconflict
    · apply mem_union_right
      rw [mem_deletedNeighbors_iff]
      exact ⟨hr, hforbidden⟩
  exact ((card_le_card hsub).trans (card_union_le _ _)).trans
    (Nat.add_le_add_left (sampledLinkForbiddenPair_right_card_le F I D P Q K R hP hR b) _)

end

end Erdos207
