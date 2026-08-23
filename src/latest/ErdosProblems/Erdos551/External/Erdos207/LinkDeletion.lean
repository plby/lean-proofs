/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.MasterCrossingCoverStage

/-!
# The concrete deletion relation in a sparsified link

A sampled link pair is deleted for exactly two reasons: its triple shares a
covered pair with the current packing, or it participates in a forbidden
configuration contained in the current packing plus the sampled reservoir.
With this definition, both structural safety obligations of the robust
matching cover become tautological; only the maximum left deletion degree
remains to be estimated.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Candidate pairs are precisely those whose link triple is in the current
available family. -/
def linkAvailableRelation
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (available : TripleSystemOn V)
    (a : ↥K.left) (b : ↥K.right) : Prop :=
  linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
    K.center_ne_left K.center_ne_right K.left_ne_right a b ∈ available

instance linkAvailableRelation.instDecidableRel
    {V : Type*} [DecidableEq V]
    (K : BipartiteLink V) (available : TripleSystemOn V) :
    DecidableRel (linkAvailableRelation K available) := by
  intro a b
  unfold linkAvailableRelation
  infer_instance

/-- Exact pair-conflict/forbidden-participation deletion predicate for one
sampled bipartite link. -/
def linkDeleted
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right))
    (a : ↥K.left) (b : ↥K.right) : Prop :=
  let T := linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
    K.center_ne_left K.center_ne_right K.left_ne_right a b
  ¬ TriangleAvoidsGraph (coveredGraph P) T ∨
    ParticipatesForbidden F P
      (linkReservoirTriangles K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right R) T

noncomputable instance linkDeleted.instDecidableRel
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (K : BipartiteLink V) (R : Finset (↥K.left × ↥K.right)) :
    DecidableRel (linkDeleted F P K R) := by
  intro a b
  exact Classical.propDecidable _

lemma linkDeleted_survivor_avoids
    {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {K : BipartiteLink V} {R : Finset (↥K.left × ↥K.right)}
    {a : ↥K.left} {b : ↥K.right}
    (h : ¬ linkDeleted F P K R a b) :
    TriangleAvoidsGraph (coveredGraph P)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b) := by
  exact not_not.mp (not_or.mp h).1

lemma linkDeleted_survivor_nonparticipating
    {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {K : BipartiteLink V} {R : Finset (↥K.left × ↥K.right)}
    {a : ↥K.left} {b : ↥K.right}
    (h : ¬ linkDeleted F P K R a b) :
    ¬ ParticipatesForbidden F P
      (linkReservoirTriangles K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right R)
      (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
        K.center_ne_left K.center_ne_right K.left_ne_right a b) := by
  exact (not_or.mp h).2

/-- Candidate count, sampling, and one concrete maximum-deletion-degree bound
produce the exact extension consumed by the multi-link iteration. -/
theorem hasLinkCoverExtension_of_candidateBound
    {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : BipartiteLink V) (Delta k : Nat)
    (hcandidates : ∀ o : HallObstruction ↥K.left ↥K.right,
      (Delta * o.1.1.card + 1) * k ≤
        (relationPairsLeaving (linkAvailableRelation K available)
          o.1.1 o.1.2).card)
    (sampleProbability : NNReal) (hprob : sampleProbability ≤ 1)
    (hsmall :
      (Fintype.card
        (Σ o : HallObstruction ↥K.left ↥K.right,
          HallGroupIndex Delta o) : NNReal) *
          (1 - sampleProbability) ^ k < 1)
    (hbalanced : K.left.card = K.right.card)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hdeleted : ∀ R a,
      (deletedNeighbors (linkDeleted F P K R) a).card ≤ Delta) :
    HasLinkCoverExtension F available P K := by
  classical
  have hcard : Fintype.card ↥K.left = Fintype.card ↥K.right := by
    simpa using hbalanced
  obtain ⟨_R, M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid,
      hleft, hright⟩ :=
    exists_safe_linkMatchingTriangles_of_candidate_bound
      K.center K.leftEmbedding K.rightEmbedding K.center_ne_left
      K.center_ne_right K.left_ne_right F P available
      (linkAvailableRelation K available) Delta k hcandidates
      sampleProbability hprob hsmall hcard hPpacking hPavoid
      (by intro a b h; exact h)
      (linkDeleted F P K)
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_avoids hsurvive)
      hdeleted
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_nonparticipating hsurvive)
  refine ⟨M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid, ?_⟩
  constructor
  · intro x hx
    exact hleft ⟨x, hx⟩
  · intro x hx
    exact hright ⟨x, hx⟩

end

end Erdos207
