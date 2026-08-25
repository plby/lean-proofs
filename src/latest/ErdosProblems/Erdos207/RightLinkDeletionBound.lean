/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkDeletionBound
import ErdosProblems.Erdos207.TwoSidedRobustMatching

/-!
# Bounding the right endpoint degree of link deletions

The two-sided robust Hall lemma needs the deletion maximum degree in both
orientations.  This file is the right-endpoint counterpart of
`LinkDeletionBound`: for fixed `b`, deleted left neighbors inject into the
edge and rooted-forbidden third-vertex blockers of the spoke `center-b`.
-/

namespace Erdos207

open Finset

noncomputable section

def linkRightPairConflictNeighbors
    {V : Type*} [DecidableEq V]
    (P : TripleSystemOn V) (K : BipartiteLink V) (b : ↥K.right) :
    Finset ↥K.left := by
  classical
  exact univ.filter fun a ↦
    ¬ TriangleAvoidsGraph (coveredGraph P)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b)

def linkRightForbiddenParticipantNeighbors
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (b : ↥K.right) : Finset ↥K.left := by
  classical
  exact univ.filter fun a ↦
    ParticipatesForbidden F P
      (linkReservoirTriangles K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right R)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b)

lemma deletedNeighbors_transpose_linkDeleted_eq_union
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (b : ↥K.right) :
    deletedNeighbors (transposeRelation (linkDeleted F P K R)) b =
      linkRightPairConflictNeighbors P K b ∪
        linkRightForbiddenParticipantNeighbors F P K R b := by
  classical
  ext a
  simp only [mem_deletedNeighbors_iff, mem_union, mem_filter, mem_univ,
    true_and, linkRightPairConflictNeighbors,
    linkRightForbiddenParticipantNeighbors, transposeRelation_apply,
    linkDeleted]

/-- Embed a left link vertex as the third vertex of the center-right pair. -/
def linkLeftThirdVertex
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (b : ↥K.right) :
    ↥K.left ↪ ThirdVertex K.center b.1 where
  toFun a := ⟨a.1, (K.center_ne_left a).symm, K.left_ne_right a b⟩
  inj' := by
    intro a c h
    apply Subtype.ext
    exact congrArg (fun w : ThirdVertex K.center b.1 ↦ w.1) h

lemma thirdVertexTriple_linkLeftThirdVertex
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (a : ↥K.left) (b : ↥K.right) :
    thirdVertexTriple (K.center_ne_right b)
        (linkLeftThirdVertex K b a) =
      linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b := by
  apply Subtype.ext
  ext x
  simp only [thirdVertexTriple, tripleOfThree, linkMatchingTriple,
    mem_insert, mem_singleton]
  tauto

private lemma center_ne_right_val
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (b : ↥K.right) : K.center ≠ b.1 :=
  K.center_ne_right b

theorem card_linkRightPairConflictNeighbors_le_edgeBlocked
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : TripleSystemOn V) (K : BipartiteLink V) (b : ↥K.right) :
    (linkRightPairConflictNeighbors P K b).card ≤
      (edgeBlockedThirdVertices (univ : TripleSystemOn V) P
        (center_ne_right_val K b)).card := by
  classical
  let e := linkLeftThirdVertex K b
  have hsub : (linkRightPairConflictNeighbors P K b).map e ⊆
      edgeBlockedThirdVertices (univ : TripleSystemOn V) P
        (center_ne_right_val K b) := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hw
    apply mem_edgeBlockedThirdVertices_iff.mpr
    constructor
    · exact mem_univ _
    · dsimp only [e]
      have htriple :
          thirdVertexTriple (center_ne_right_val K b)
              (linkLeftThirdVertex K b a) =
            linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
              K.center_ne_left K.center_ne_right K.left_ne_right a b := by
        apply Subtype.ext
        ext x
        simp only [thirdVertexTriple, tripleOfThree, linkMatchingTriple,
          mem_insert, mem_singleton]
        tauto
      rw [htriple]
      simpa only [linkRightPairConflictNeighbors, mem_filter, mem_univ,
        true_and] using ha
  calc
    (linkRightPairConflictNeighbors P K b).card =
        ((linkRightPairConflictNeighbors P K b).map e).card := by simp
    _ ≤ _ := card_le_card hsub

theorem card_linkRightForbiddenParticipantNeighbors_le_forbiddenBlocked
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (b : ↥K.right) :
    (linkRightForbiddenParticipantNeighbors F P K R b).card ≤
      (forbiddenBlockedThirdVertices F
        (univ : TripleSystemOn V)
        (P ∪ linkReservoirTriangles K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right R)
        (center_ne_right_val K b)).card := by
  classical
  let reservoir := linkReservoirTriangles K.center K.leftEmbedding
    K.rightEmbedding K.center_ne_left K.center_ne_right K.left_ne_right R
  let e := linkLeftThirdVertex K b
  have hsub : (linkRightForbiddenParticipantNeighbors F P K R b).map e ⊆
      forbiddenBlockedThirdVertices F (univ : TripleSystemOn V)
        (P ∪ reservoir) (center_ne_right_val K b) := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hw
    dsimp only [e]
    have hpart : ParticipatesForbidden F P reservoir
        (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right a b) := by
      simpa only [linkRightForbiddenParticipantNeighbors, mem_filter,
        mem_univ, true_and, reservoir] using ha
    obtain ⟨C, hCF, hTC, hCsub⟩ := hpart
    apply mem_forbiddenBlockedThirdVertices_iff.mpr
    have htriple :
        thirdVertexTriple (center_ne_right_val K b)
            (linkLeftThirdVertex K b a) =
          linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
            K.center_ne_left K.center_ne_right K.left_ne_right a b := by
      apply Subtype.ext
      ext x
      simp only [thirdVertexTriple, tripleOfThree, linkMatchingTriple,
        mem_insert, mem_singleton]
      tauto
    rw [htriple]
    refine ⟨mem_univ _, C, hCF, hTC, ?_⟩
    intro S hSerase
    exact hCsub (mem_erase.mp hSerase).2
  calc
    (linkRightForbiddenParticipantNeighbors F P K R b).card =
        ((linkRightForbiddenParticipantNeighbors F P K R b).map e).card :=
      by simp
    _ ≤ _ := by simpa only [reservoir] using card_le_card hsub

/-- Exact maximum-degree estimate for the transposed concrete deletion
relation. -/
theorem card_deletedNeighbors_transpose_linkDeleted_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (b : ↥K.right) (hleave : (leaveGraph P).Adj K.center b.1)
    (k : ℕ) (hfamily : ∀ C ∈ F, C.card ≤ k) :
    (deletedNeighbors (transposeRelation (linkDeleted F P K R)) b).card ≤
      (coveredGraph P).degree K.center + (coveredGraph P).degree b.1 +
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center b.1).card * k := by
  rw [deletedNeighbors_transpose_linkDeleted_eq_union]
  calc
    (linkRightPairConflictNeighbors P K b ∪
        linkRightForbiddenParticipantNeighbors F P K R b).card ≤
      (linkRightPairConflictNeighbors P K b).card +
        (linkRightForbiddenParticipantNeighbors F P K R b).card :=
      card_union_le _ _
    _ ≤ (edgeBlockedThirdVertices (univ : TripleSystemOn V) P
          (K.center_ne_right b)).card +
        (forbiddenBlockedThirdVertices F
          (univ : TripleSystemOn V)
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) (K.center_ne_right b)).card :=
      Nat.add_le_add
        (card_linkRightPairConflictNeighbors_le_edgeBlocked P K b)
        (card_linkRightForbiddenParticipantNeighbors_le_forbiddenBlocked
          F P K R b)
    _ ≤ ((coveredGraph P).degree K.center +
          (coveredGraph P).degree b.1) +
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center b.1).card * k :=
      Nat.add_le_add
        (card_edgeBlockedThirdVertices_le_degree_add
          (A := (univ : TripleSystemOn V)) hleave)
        (card_forbiddenBlockedThirdVertices_le_mul_rooted_active
          (A := (univ : TripleSystemOn V))
          (P := P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) (K.center_ne_right b) hfamily)
    _ = _ := by omega

end

end Erdos207
