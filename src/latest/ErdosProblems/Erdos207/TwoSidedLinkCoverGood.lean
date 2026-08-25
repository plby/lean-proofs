/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoSidedRandomRobustMatchingGood
import ErdosProblems.Erdos207.TwoSidedLinkCover

/-!
# Safe link covers with a high-probability rooted cutoff

The robust-Hall sample and the rooted-threat cutoff are selected on the same
Bernoulli outcome.  Thus the deletion bound only needs the cutoff for that
chosen reservoir, exactly as in the KSSS link step.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A two-sided robust sample satisfying an extra reservoir predicate gives
a safe matching cover whenever the concrete deletion relation is bounded on
reservoirs satisfying that predicate. -/
theorem exists_safe_linkMatchingTriangles_of_twoSided_candidate_bound_with_good
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (F : ForbiddenFamilyOn V) (P available : TripleSystemOn V)
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize : ℕ)
    (hcandidates : ∀ o : OrientedSmallHallObstruction A B,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates r o).card)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (Good : Finset (A × B) → Prop) (epsilon : ℝ≥0)
    (hbad : (FiniteLaw.independentBits
      (fun _ : A × B ↦ sampleProbability) (fun _ ↦ hprob)).probability
        (fun omega ↦ ¬ Good (FiniteLaw.selectedByBits omega)) ≤ epsilon)
    (hsmall : epsilon +
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction A B,
          OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hcard : Fintype.card A = Fintype.card B)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ a b, r a b →
      linkMatchingTriple center left right hcenterLeft hcenterRight
        hleftRight a b ∈ available)
    (deleted : Finset (A × B) → A → B → Prop)
    [deletedDecidable : ∀ R, DecidableRel (deleted R)]
    (havoidsOld : ∀ R a b, r a b → (a, b) ∈ R →
      ¬ deleted R a b →
      TriangleAvoidsGraph (coveredGraph P)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b))
    (hleftDeleted : ∀ R, Good R → ∀ a,
      (deletedNeighbors (deleted R) a).card ≤ Delta)
    (hrightDeleted : ∀ R, Good R → ∀ b,
      (deletedNeighbors (transposeRelation (deleted R)) b).card ≤ Delta)
    (hsafe : ∀ R a b, r a b → (a, b) ∈ R → ¬ deleted R a b →
      ¬ ParticipatesForbidden F P
        (linkReservoirTriangles center left right hcenterLeft hcenterRight
          hleftRight R)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b)) :
    ∃ R : Finset (A × B), Good R ∧
      ∃ M : TripleSystemOn V,
        M ⊆ available ∧
        M ⊆ linkReservoirTriangles center left right hcenterLeft
          hcenterRight hleftRight R ∧
        Disjoint P M ∧ IsPackingOn (P ∪ M) ∧
        AvoidsForbidden (P ∪ M) F ∧
        (∀ a, (coveredGraph M).Adj center (left a)) ∧
        (∀ b, (coveredGraph M).Adj center (right b)) := by
  classical
  obtain ⟨R, hRgood, hmatching⟩ :=
    exists_bijective_twoSided_robust_matching_sample_with_good
      r Delta groupSize hcandidates sampleProbability hprob Good epsilon
        hbad hsmall hcard
  obtain ⟨M, hM⟩ := exists_safe_linkMatchingTriangles_of_twoSided_sample
    center left right hcenterLeft hcenterRight hleftRight F P available
      r Delta R hmatching hPpacking hPavoid havailable (deleted R)
      (havoidsOld R) (hleftDeleted R hRgood) (hrightDeleted R hRgood)
      (hsafe R)
  exact ⟨R, hRgood, M, hM⟩

/-- Degree bounds and a high-probability rooted cutoff discharge the concrete
pair-conflict and forbidden-participation deletions for one link. -/
theorem hasLinkCoverExtension_of_twoSided_degree_rooted_probability
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : BipartiteLink V) (Delta groupSize degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hcandidates : ∀ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates
          (linkAvailableRelation K available) o).card)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (epsilon : ℝ≥0)
    (hrootBad : (FiniteLaw.independentBits
      (fun _ : ↥K.left × ↥K.right ↦ sampleProbability)
      (fun _ ↦ hprob)).probability (fun omega ↦
        ¬ ((∀ a : ↥K.left,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center a.1).card ≤ rootCutoff) ∧
        (∀ b : ↥K.right,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center b.1).card ≤ rootCutoff))) ≤ epsilon)
    (hsmall : epsilon +
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
          OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
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
    (hscalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasLinkCoverExtension F available P K := by
  classical
  let Good : Finset (↥K.left × ↥K.right) → Prop := fun R ↦
    (∀ a : ↥K.left,
      (rootedActiveForbiddenConfigurations F
        (P ∪ linkReservoirTriangles K.center K.leftEmbedding
          K.rightEmbedding K.center_ne_left K.center_ne_right
          K.left_ne_right R) K.center a.1).card ≤ rootCutoff) ∧
    (∀ b : ↥K.right,
      (rootedActiveForbiddenConfigurations F
        (P ∪ linkReservoirTriangles K.center K.leftEmbedding
          K.rightEmbedding K.center_ne_left K.center_ne_right
          K.left_ne_right R) K.center b.1).card ≤ rootCutoff)
  have hcard : Fintype.card ↥K.left = Fintype.card ↥K.right := by
    simpa using hbalanced
  obtain ⟨R, _hRgood, M, hMavailable, _hMreservoir,
      hPMdisjoint, hPMpacking,
      hPMavoid, hleft, hright⟩ :=
    exists_safe_linkMatchingTriangles_of_twoSided_candidate_bound_with_good
      K.center K.leftEmbedding K.rightEmbedding K.center_ne_left
      K.center_ne_right K.left_ne_right F P available
      (linkAvailableRelation K available) Delta groupSize hcandidates
      sampleProbability hprob Good epsilon (by
        simpa only [Good] using hrootBad) hsmall hcard hPpacking hPavoid
      (by intro a b h; exact h) (linkDeleted F P K)
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_avoids hsurvive)
      (by
        intro R hgood a
        exact (card_deletedNeighbors_linkDeleted_le F P K R a
          (hleaveLeft a) familyCutoff hfamily).trans <| by
            exact (Nat.add_le_add (hdegreeLeft a)
              (Nat.mul_le_mul_right familyCutoff (hgood.1 a))).trans hscalar)
      (by
        intro R hgood b
        exact (card_deletedNeighbors_transpose_linkDeleted_le F P K R b
          (hleaveRight b) familyCutoff hfamily).trans <| by
            exact (Nat.add_le_add (hdegreeRight b)
              (Nat.mul_le_mul_right familyCutoff (hgood.2 b))).trans hscalar)
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_nonparticipating hsurvive)
  refine ⟨M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid, ?_⟩
  exact ⟨fun x hx ↦ hleft ⟨x, hx⟩,
    fun x hx ↦ hright ⟨x, hx⟩⟩

end

end Erdos207
