/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RobustHallSamplingScalar
import ErdosProblems.Erdos207.TwoSidedLinkCoverGood

/-!
# Scalar robust Hall with a probabilistic rooted cutoff

This is the quantitative single-link endpoint used by KSSS: the Hall group
failure estimate and the rooted-threat failure estimate share one union
bound.  The rooted cutoff is required only for the selected reservoir.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The explicit obstruction-count scalar remains valid after adding an
extra failure budget. -/
lemma orientedSmallHall_sampling_add_lt_one_of_scalar
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (Delta groupSize : ℕ) (sampleProbability epsilon : ℝ≥0)
    (hcard : Fintype.card A = Fintype.card B)
    (hsmall : epsilon +
      (2 * 4 ^ Fintype.card B *
          (Delta * Fintype.card B + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1) :
    epsilon + (Fintype.card
      (Σ o : OrientedSmallHallObstruction A B,
        OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
      (1 - sampleProbability) ^ groupSize < 1 := by
  apply lt_of_le_of_lt _ hsmall
  have hcount :
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction A B,
          OrientedSmallHallGroupIndex Delta o) : ℝ≥0) ≤
        (2 * 4 ^ Fintype.card B *
          (Delta * Fintype.card B + 1) : ℕ) := by
    exact_mod_cast card_orientedSmallHallGroupSigma_le Delta hcard
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one] using
    add_le_add_right
      (mul_le_mul_of_nonneg_right hcount
        (show (0 : ℝ≥0) ≤ (1 - sampleProbability) ^ groupSize from
          zero_le)) epsilon

/-- Fully scalar mixing, sampling, degree, and deletion hypotheses, together
with a high-probability rooted cutoff for the Bernoulli link reservoir,
produce a safe covering extension. -/
theorem HasLinkDegreeCodegreeBounds.hasLinkCoverExtension_of_scalars_good
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {available P : TripleSystemOn V}
    {K : BipartiteLink V} {d D codegree : ℕ}
    (htyp : HasLinkDegreeCodegreeBounds available K d D codegree)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hbalanced : K.left.card = K.right.card)
    (hpositive : 0 < K.right.card)
    (hdensityLe : density ≤ d)
    (hmixingScalar : ∀ s : ℕ, cutoff < s → s ≤ K.right.card →
      K.right.card * (D + codegree * s) <
        s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdensityScalar : K.right.card * candidate ≤
      density * (K.right.card / 2))
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
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
    (hsampleScalar : epsilon +
      (2 * 4 ^ K.right.card *
          (Delta * K.right.card + 1) : ℝ≥0) *
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
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasLinkCoverExtension F available P K := by
  have hmoments := balancedLink_secondMomentScalars_of_uniform K d D
    codegree density cutoff hbalanced hpositive hdensityLe hmixingScalar
  have hcandidates := htyp.orientedSmallHallCandidateBound
    Delta groupSize density candidate cutoff hbalanced hpositive
      hmoments.1 hmoments.2 hdegreeScalar hdensityScalar hcandidateScalar
  have hcard : Fintype.card ↥K.left = Fintype.card ↥K.right := by
    simpa using hbalanced
  have hsample := orientedSmallHall_sampling_add_lt_one_of_scalar
    Delta groupSize sampleProbability epsilon hcard (by
      simpa using hsampleScalar)
  exact hasLinkCoverExtension_of_twoSided_degree_rooted_probability
    F available P K Delta groupSize degreeCutoff rootCutoff familyCutoff
      hcandidates sampleProbability hprob epsilon hrootBad hsample hbalanced
      hPpacking hPavoid hfamily hleaveLeft hleaveRight hdegreeLeft
      hdegreeRight hdeletionScalar

end

end Erdos207
