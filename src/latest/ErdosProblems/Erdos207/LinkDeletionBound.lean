/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkDeletion
import ErdosProblems.Erdos207.ForbiddenCompletionCount

/-!
# Bounding the concrete link deletion degree

For a fixed left link vertex, right vertices deleted by pair conflicts inject
into the usual edge-blocked third vertices.  Right vertices deleted by
forbidden participation inject into forbidden-blocked third vertices rooted
at the center-left pair, after adjoining the whole sampled reservoir.  The
standard degree and rooted-active estimates therefore give the exact bound

`coveredDegree center + coveredDegree left + rootedCount * familyCutoff`.
-/

namespace Erdos207

open Finset

noncomputable section

def linkPairConflictNeighbors
    {V : Type*} [DecidableEq V]
    (P : TripleSystemOn V) (K : BipartiteLink V) (a : ↥K.left) :
    Finset ↥K.right := by
  classical
  exact Finset.univ.filter fun b ↦
    ¬ TriangleAvoidsGraph (coveredGraph P)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b)

def linkForbiddenParticipantNeighbors
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) : Finset ↥K.right := by
  classical
  exact Finset.univ.filter fun b ↦
    ParticipatesForbidden F P
      (linkReservoirTriangles K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right R)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b)

lemma deletedNeighbors_linkDeleted_eq_union
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) :
    deletedNeighbors (linkDeleted F P K R) a =
      linkPairConflictNeighbors P K a ∪
        linkForbiddenParticipantNeighbors F P K R a := by
  classical
  ext b
  simp only [mem_deletedNeighbors_iff, mem_union, mem_filter, mem_univ,
    true_and, linkPairConflictNeighbors, linkForbiddenParticipantNeighbors,
    linkDeleted]

/-- Embed a right link vertex as the third vertex of the center-left pair. -/
def linkRightThirdVertex
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (a : ↥K.left) :
    ↥K.right ↪ ThirdVertex K.center a.1 where
  toFun b := ⟨b.1, (K.center_ne_right b).symm,
    (K.left_ne_right a b).symm⟩
  inj' := by
    intro b c h
    apply Subtype.ext
    exact congrArg (fun w : ThirdVertex K.center a.1 ↦ w.1) h

lemma thirdVertexTriple_linkRightThirdVertex
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (a : ↥K.left) (b : ↥K.right) :
    thirdVertexTriple (K.center_ne_left a)
        (linkRightThirdVertex K a b) =
      linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b := by
  apply Subtype.ext
  rfl

private lemma center_ne_left_val
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (a : ↥K.left) : K.center ≠ a.1 := by
  exact K.center_ne_left a

/-- Pair-conflict deletions inject into the standard edge-blocker set for
the center-left spoke. -/
theorem card_linkPairConflictNeighbors_le_edgeBlocked
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : TripleSystemOn V) (K : BipartiteLink V) (a : ↥K.left) :
    (linkPairConflictNeighbors P K a).card ≤
      (edgeBlockedThirdVertices (Finset.univ : TripleSystemOn V) P
        (center_ne_left_val K a)).card := by
  classical
  let e := linkRightThirdVertex K a
  have hsub : (linkPairConflictNeighbors P K a).map e ⊆
      edgeBlockedThirdVertices (Finset.univ : TripleSystemOn V) P
        (center_ne_left_val K a) := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hw
    apply mem_edgeBlockedThirdVertices_iff.mpr
    constructor
    · exact mem_univ _
    · dsimp only [e]
      have htriple :
          thirdVertexTriple (center_ne_left_val K a)
              (linkRightThirdVertex K a b) =
            linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
              K.center_ne_left K.center_ne_right K.left_ne_right a b := by
        apply Subtype.ext
        rfl
      rw [htriple]
      simpa only [linkPairConflictNeighbors, mem_filter, mem_univ,
        true_and] using hb
  calc
    (linkPairConflictNeighbors P K a).card =
        ((linkPairConflictNeighbors P K a).map e).card := by simp
    _ ≤ _ := card_le_card hsub

/-- Forbidden-participation deletions inject into standard forbidden
third-vertex blockers after the whole sampled reservoir is adjoined. -/
theorem card_linkForbiddenParticipantNeighbors_le_forbiddenBlocked
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) :
    (linkForbiddenParticipantNeighbors F P K R a).card ≤
      (forbiddenBlockedThirdVertices F
        (Finset.univ : TripleSystemOn V)
        (P ∪ linkReservoirTriangles K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right R)
        (center_ne_left_val K a)).card := by
  classical
  let reservoir := linkReservoirTriangles K.center K.leftEmbedding
    K.rightEmbedding K.center_ne_left K.center_ne_right K.left_ne_right R
  let e := linkRightThirdVertex K a
  have hsub : (linkForbiddenParticipantNeighbors F P K R a).map e ⊆
      forbiddenBlockedThirdVertices F (Finset.univ : TripleSystemOn V)
        (P ∪ reservoir) (center_ne_left_val K a) := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hw
    dsimp only [e]
    have htriple :
        thirdVertexTriple (center_ne_left_val K a)
            (linkRightThirdVertex K a b) =
          linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
            K.center_ne_left K.center_ne_right K.left_ne_right a b := by
      apply Subtype.ext
      rfl
    have hpart : ParticipatesForbidden F P reservoir
        (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right a b) := by
      simpa only [linkForbiddenParticipantNeighbors, mem_filter, mem_univ,
        true_and, reservoir] using hb
    obtain ⟨C, hCF, hTC, hCsub⟩ := hpart
    apply mem_forbiddenBlockedThirdVertices_iff.mpr
    rw [htriple]
    refine ⟨mem_univ _, C, hCF, hTC, ?_⟩
    intro S hSerase
    exact hCsub (mem_erase.mp hSerase).2
  calc
    (linkForbiddenParticipantNeighbors F P K R a).card =
        ((linkForbiddenParticipantNeighbors F P K R a).map e).card := by simp
    _ ≤ _ := by simpa only [reservoir] using card_le_card hsub

/-- Exact deterministic maximum-degree estimate for the concrete deletion
relation. -/
theorem card_deletedNeighbors_linkDeleted_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) (hleave : (leaveGraph P).Adj K.center a.1)
    (k : Nat) (hfamily : ∀ C ∈ F, C.card ≤ k) :
    (deletedNeighbors (linkDeleted F P K R) a).card ≤
      (coveredGraph P).degree K.center + (coveredGraph P).degree a.1 +
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center a.1).card * k := by
  rw [deletedNeighbors_linkDeleted_eq_union]
  calc
    (linkPairConflictNeighbors P K a ∪
        linkForbiddenParticipantNeighbors F P K R a).card ≤
      (linkPairConflictNeighbors P K a).card +
        (linkForbiddenParticipantNeighbors F P K R a).card :=
      card_union_le _ _
    _ ≤ (edgeBlockedThirdVertices (Finset.univ : TripleSystemOn V) P
          (K.center_ne_left a)).card +
        (forbiddenBlockedThirdVertices F
          (Finset.univ : TripleSystemOn V)
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) (K.center_ne_left a)).card :=
      Nat.add_le_add
        (card_linkPairConflictNeighbors_le_edgeBlocked P K a)
        (card_linkForbiddenParticipantNeighbors_le_forbiddenBlocked F P K R a)
    _ ≤ ((coveredGraph P).degree K.center +
          (coveredGraph P).degree a.1) +
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center a.1).card * k :=
      Nat.add_le_add
        (card_edgeBlockedThirdVertices_le_degree_add
          (A := (Finset.univ : TripleSystemOn V)) hleave)
        (card_forbiddenBlockedThirdVertices_le_mul_rooted_active
          (A := (Finset.univ : TripleSystemOn V))
          (P := P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) (K.center_ne_left a) hfamily)
    _ = _ := by omega

/-- Degree and rooted-active cutoffs discharge the concrete deletion premise
of the robust link-cover theorem. -/
theorem hasLinkCoverExtension_of_degree_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : BipartiteLink V) (Delta groupSize degreeCutoff rootCutoff
      familyCutoff : Nat)
    (hcandidates : ∀ o : HallObstruction ↥K.left ↥K.right,
      (Delta * o.1.1.card + 1) * groupSize ≤
        (relationPairsLeaving (linkAvailableRelation K available)
          o.1.1 o.1.2).card)
    (sampleProbability : NNReal) (hprob : sampleProbability ≤ 1)
    (hsmall :
      (Fintype.card
        (Σ o : HallObstruction ↥K.left ↥K.right,
          HallGroupIndex Delta o) : NNReal) *
          (1 - sampleProbability) ^ groupSize < 1)
    (hbalanced : K.left.card = K.right.card)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hleave : ∀ a : ↥K.left, (leaveGraph P).Adj K.center a.1)
    (hdegree : ∀ a : ↥K.left,
      (coveredGraph P).degree K.center + (coveredGraph P).degree a.1 ≤
        degreeCutoff)
    (hroot : ∀ (R : Finset (↥K.left × ↥K.right)) (a : ↥K.left),
      (rootedActiveForbiddenConfigurations F
        (P ∪ linkReservoirTriangles K.center K.leftEmbedding
          K.rightEmbedding K.center_ne_left K.center_ne_right
          K.left_ne_right R) K.center a.1).card ≤ rootCutoff)
    (hscalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasLinkCoverExtension F available P K := by
  apply hasLinkCoverExtension_of_candidateBound F available P K Delta
    groupSize hcandidates sampleProbability hprob hsmall hbalanced
      hPpacking hPavoid
  intro R a
  exact (card_deletedNeighbors_linkDeleted_le F P K R a (hleave a)
    familyCutoff hfamily).trans <| by
      exact (Nat.add_le_add (hdegree a)
        (Nat.mul_le_mul_right familyCutoff (hroot R a))).trans hscalar

end

end Erdos207
