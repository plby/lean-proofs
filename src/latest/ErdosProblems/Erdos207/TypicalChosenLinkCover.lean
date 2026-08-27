/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationChosenLink
import ErdosProblems.Erdos207.TwoSidedLinkCover

/-!
# From a typical chosen link to a safe covering matching

This file composes the corrected two-sided Hall calculation with the exact
pair-conflict and forbidden-participation deletion bounds.  It is the final
single-center interface needed by the chosen-link master cover stage.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Degree/codegree typicality and the explicit robust-Hall, sampling, and
deletion inequalities produce a safe link-cover extension. -/
theorem HasLinkDegreeCodegreeBounds.hasLinkCoverExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {available P : TripleSystemOn V}
    {K : BipartiteLink V} {d D codegree : ℕ}
    (htyp : HasLinkDegreeCodegreeBounds available K d D codegree)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hbalanced : K.left.card = K.right.card)
    (hpositive : 0 < K.right.card)
    (hleftSecondMomentScalar :
      ∀ S : Finset ↥K.left, ∀ U : Finset ↥K.right, cutoff < S.card →
        K.right.card ^ 2 * (K.right.card - U.card) *
            (D * S.card + codegree * S.card * (S.card - 1)) <
          (K.right.card * d * S.card -
            density * S.card * U.card) ^ 2)
    (hrightSecondMomentScalar :
      ∀ S : Finset ↥K.right, ∀ U : Finset ↥K.left, cutoff < S.card →
        K.left.card ^ 2 * (K.left.card - U.card) *
            (D * S.card + codegree * S.card * (S.card - 1)) <
          (K.left.card * d * S.card -
            density * S.card * U.card) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdensityScalar : K.right.card * candidate ≤
      density * (K.right.card / 2))
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (hsample :
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
          OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
          (1 - sampleProbability) ^ groupSize < 1)
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
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasLinkCoverExtension F available P K := by
  have hcandidates := htyp.orientedSmallHallCandidateBound
    Delta groupSize density candidate cutoff hbalanced hpositive
      hleftSecondMomentScalar hrightSecondMomentScalar hdegreeScalar
      hdensityScalar hcandidateScalar
  exact hasLinkCoverExtension_of_twoSided_degree_rooted
    F available P K Delta groupSize degreeCutoff rootCutoff familyCutoff
      hcandidates sampleProbability hprob hsample hbalanced hPpacking hPavoid
      hfamily hleaveLeft hleaveRight hdegreeLeft hdegreeRight hrootLeft
      hrootRight hdeletionScalar

end

end Erdos207
