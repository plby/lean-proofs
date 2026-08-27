/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationChosenLinkCover
import ErdosProblems.Erdos207.RobustHallSamplingScalarGood
import ErdosProblems.Erdos207.DynamicResidualStructure
import ErdosProblems.Erdos207.LinkSideDensityScalar

/-!
# Chosen residual links with probabilistic rooted control

This is the KSSS single-center interface.  The rooted cutoff is proved for
the actual Bernoulli reservoir with high probability and is selected jointly
with all robust-Hall witness events.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsIterationTypical.exists_chosenResidualLinkCover_good_of_supported
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (center : V) (hcInner : center ∉ W.U i.succ)
    (hresInner : residualNeighbors G P center ⊆ W.U i.succ)
    (heven : Even (residualNeighbors G P center).card)
    (m d D codegree loss : ℕ)
    (hcovered : (coveredGraph P).degree center ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ((residualNeighbors G P center).card : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixingScalar : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K → 0 < K.right.card →
      ∀ s : ℕ, cutoff < s → s ≤ K.right.card →
        K.right.card * (D + codegree * s) <
          s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdTwo : 2 ≤ d)
    (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (epsilon : ℝ≥0)
    (hrootBad : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K → 0 < K.right.card →
      (FiniteLaw.independentBits
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
    (hsampleScalar : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K → 0 < K.right.card →
      epsilon + (2 * 4 ^ K.right.card *
          (Delta * K.right.card + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hdegree : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K →
      (∀ a : ↥K.left,
        (coveredGraph P).degree K.center +
          (coveredGraph P).degree a.1 ≤ degreeCutoff) ∧
      (∀ b : ↥K.right,
        (coveredGraph P).degree K.center +
          (coveredGraph P).degree b.1 ≤ degreeCutoff))
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    ∃ K : BipartiteLink V,
      IsResidualBipartition G P center K ∧
      HasLinkCoverExtension F A P K := by
  by_cases hne : (residualNeighbors G P center).Nonempty
  · obtain ⟨K, hK, hKtyp⟩ :=
      htyp.exists_chosenResidualLink_of_supported htri i hki hGsupp center
        hcInner hresInner heven m d D codegree loss hcovered hh hlower
        hupper hcodegree hbisection
    have hpositive := hK.right_card_pos hne
    refine ⟨K, hK, ?_⟩
    exact hKtyp.hasLinkCoverExtension_of_scalars_good Delta groupSize
      density candidate cutoff degreeCutoff rootCutoff familyCutoff
      hK.2.2 hpositive hdensityLe (hmixingScalar K hK hpositive)
      hdegreeScalar
      (hKtyp.candidate_density_scalar_of_three hK.2.2 hpositive hdTwo
        hdensityScalar)
      hcandidateScalar
      sampleProbability hprob epsilon (hrootBad K hK hpositive)
      (hsampleScalar K hK hpositive) hPpacking hPavoid hfamily
      (hK.leave_sides).1 (hK.leave_sides).2 (hdegree K hK).1
      (hdegree K hK).2 hdeletionScalar
  · have hempty : residualNeighbors G P center = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    refine ⟨emptyBipartiteLink center, ?_,
      emptyBipartiteLink_hasLinkCoverExtension F A P center hPpacking
        hPavoid⟩
    exact ⟨rfl, by simp [hempty], by simp⟩

end

end Erdos207
