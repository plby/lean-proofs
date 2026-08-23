/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.TwoSidedRandomLinkMatchingCover
import ErdosProblems.Erdos551.External.Erdos207.RightLinkDeletionBound

/-!
# Concrete two-sided robust link-cover endpoint

The hypotheses of this file are now exactly the estimates left by the KSSS
typical-link and rooted-moment arguments: two-oriented small-Hall candidate
counts, a finite sampling union bound, degree cutoffs at every link endpoint,
and rooted forbidden cutoffs at every endpoint.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Two-sided candidate counts and concrete degree/rooted cutoffs produce the
state-dependent link extension consumed by the all-center iteration. -/
theorem hasLinkCoverExtension_of_twoSided_degree_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : BipartiteLink V)
    (Delta groupSize degreeCutoff rootCutoff familyCutoff : ℕ)
    (hcandidates :
      ∀ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
        (Delta * orientedSmallHallSize o + 1) * groupSize ≤
          (orientedSmallHallCandidates
            (linkAvailableRelation K available) o).card)
    (sampleProbability : NNReal) (hprob : sampleProbability ≤ 1)
    (hsmall :
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
          OrientedSmallHallGroupIndex Delta o) : NNReal) *
          (1 - sampleProbability) ^ groupSize < 1)
    (hbalanced : K.left.card = K.right.card)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hleaveLeft : ∀ a : ↥K.left,
      (leaveGraph P).Adj K.center a.1)
    (hleaveRight : ∀ b : ↥K.right,
      (leaveGraph P).Adj K.center b.1)
    (hdegreeLeft : ∀ a : ↥K.left,
      (coveredGraph P).degree K.center + (coveredGraph P).degree a.1 ≤
        degreeCutoff)
    (hdegreeRight : ∀ b : ↥K.right,
      (coveredGraph P).degree K.center + (coveredGraph P).degree b.1 ≤
        degreeCutoff)
    (hrootLeft :
      ∀ (R : Finset (↥K.left × ↥K.right)) (a : ↥K.left),
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center a.1).card ≤ rootCutoff)
    (hrootRight :
      ∀ (R : Finset (↥K.left × ↥K.right)) (b : ↥K.right),
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center b.1).card ≤ rootCutoff)
    (hscalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasLinkCoverExtension F available P K := by
  classical
  have hcard : Fintype.card ↥K.left = Fintype.card ↥K.right := by
    simpa using hbalanced
  obtain ⟨_R, M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid,
      hleft, hright⟩ :=
    exists_safe_linkMatchingTriangles_of_twoSided_candidate_bound
      K.center K.leftEmbedding K.rightEmbedding K.center_ne_left
      K.center_ne_right K.left_ne_right F P available
      (linkAvailableRelation K available) Delta groupSize hcandidates
      sampleProbability hprob hsmall hcard hPpacking hPavoid
      (by intro a b h; exact h)
      (linkDeleted F P K)
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_avoids hsurvive)
      (by
        intro R a
        exact (card_deletedNeighbors_linkDeleted_le
          F P K R a (hleaveLeft a) familyCutoff hfamily).trans <| by
            exact (Nat.add_le_add (hdegreeLeft a)
              (Nat.mul_le_mul_right familyCutoff (hrootLeft R a))).trans
                hscalar)
      (by
        intro R b
        exact (card_deletedNeighbors_transpose_linkDeleted_le
          F P K R b (hleaveRight b) familyCutoff hfamily).trans <| by
            exact (Nat.add_le_add (hdegreeRight b)
              (Nat.mul_le_mul_right familyCutoff (hrootRight R b))).trans
                hscalar)
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_nonparticipating hsurvive)
  refine ⟨M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid, ?_⟩
  exact ⟨fun x hx ↦ hleft ⟨x, hx⟩,
    fun x hx ↦ hright ⟨x, hx⟩⟩

end

end Erdos207
