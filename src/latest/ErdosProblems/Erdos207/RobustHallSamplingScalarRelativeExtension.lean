/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RobustHallSamplingScalarGood
import ErdosProblems.Erdos207.TwoSidedLinkCoverRelativeExtension

/-!
# Scalar robust Hall with relative-extension preservation

This is the scalar form of the single-link theorem in which the rooted and
relative-extension failure probabilities share the robust-Hall union bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem HasLinkDegreeCodegreeBounds.exists_linkCover_of_scalars_good_extension
    {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V]
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
    (epsilonRoot : ℝ≥0)
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
            K.center b.1).card ≤ rootCutoff))) ≤ epsilonRoot)
    (configurations : J → TripleSystemOn V)
    (futureWeight totalWeight : TripleOn V → ℝ≥0) (configurationSize : ℕ)
    (hconfigCard : ∀ j, (configurations j \ P).card ≤ configurationSize)
    (hweight : ∀ T,
      linkReservoirPointWeight K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right
          sampleProbability T + futureWeight T ≤ totalWeight T)
    (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound (fun j ↦ configurations j \ P)
      totalWeight kappa)
    (hkappaOut : 0 < kappaOut)
    (epsilonExtension : ℝ≥0)
    (hepsilonExtension :
      (configurationRoots (fun j ↦ configurations j \ P)).card *
        (kappa / kappaOut) ≤ epsilonExtension)
    (hsampleScalar : (epsilonRoot + epsilonExtension) +
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
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (hfutureWeight : ∀ T, futureWeight T ≤ 1) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P M ∧
      IsPackingOn (P ∪ M) ∧ AvoidsForbidden (P ∪ M) F ∧
      CoversBipartiteLink K M ∧
      HasExtensionBound
        (fun j ↦ configurations j \ (P ∪ M)) futureWeight kappaOut := by
  have hmoments := balancedLink_secondMomentScalars_of_uniform K d D
    codegree density cutoff hbalanced hpositive hdensityLe hmixingScalar
  have hcandidates := htyp.orientedSmallHallCandidateBound
    Delta groupSize density candidate cutoff hbalanced hpositive
      hmoments.1 hmoments.2 hdegreeScalar hdensityScalar hcandidateScalar
  have hcard : Fintype.card ↥K.left = Fintype.card ↥K.right := by
    simpa using hbalanced
  have hsample := orientedSmallHall_sampling_add_lt_one_of_scalar
    Delta groupSize sampleProbability (epsilonRoot + epsilonExtension)
      hcard (by simpa using hsampleScalar)
  exact exists_linkCover_of_twoSided_degree_rooted_probability_with_extension
    F available P K Delta groupSize degreeCutoff rootCutoff familyCutoff
      hcandidates sampleProbability hprob epsilonRoot hrootBad
      configurations futureWeight totalWeight configurationSize hconfigCard
      hweight kappa kappaOut hkappa hkappaOut epsilonExtension
      hepsilonExtension hsample hbalanced hPpacking hPavoid hfamily
      hleaveLeft hleaveRight hdegreeLeft hdegreeRight hdeletionScalar
      hfutureWeight

end

end Erdos207
