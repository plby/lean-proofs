/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationChosenLink
import ErdosProblems.Erdos207.RobustHallSamplingScalar

/-!
# Choosing and safely covering one current residual link

This file joins the paired balanced-bisection theorem to the fully scalar
two-sided Hall theorem.  Empty residual links are handled without invoking
Hall, while a nonempty balanced partition automatically has two nonempty
sides.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The empty link is covered by the empty extension. -/
lemma emptyBipartiteLink_hasLinkCoverExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (center : V) (hpacking : IsPackingOn P)
    (havoid : AvoidsForbidden P F) :
    HasLinkCoverExtension F available P (emptyBipartiteLink center) := by
  refine ⟨∅, by simp, by simp, ?_, ?_, ?_⟩
  · simpa using hpacking
  · simpa using havoid
  · constructor <;> simp

/-- In a balanced partition of a nonempty residual link, each side is
nonempty. -/
lemma IsResidualBipartition.right_card_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K)
    (hne : (residualNeighbors G P center).Nonempty) :
    0 < K.right.card := by
  by_contra hzero
  have hR : K.right = ∅ := card_eq_zero.mp (by omega)
  have hLcard : K.left.card = 0 := by simpa [hR] using hK.2.2
  have hL : K.left = ∅ := card_eq_zero.mp hLcard
  have hempty : residualNeighbors G P center = ∅ := by
    rw [← hK.2.1, hL, hR]
    simp
  simpa [hempty] using hne

/-- Iteration typicality, a paired-bisection estimate, and the scalar Hall
and deletion estimates produce a chosen balanced residual link together with
a safe covering extension at the current state. -/
theorem IsIterationTypical.exists_chosenResidualLinkCover_of_supported
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
    (hdensityScalar : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K →
      K.right.card * candidate ≤ density * (K.right.card / 2))
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (hsampleScalar : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K → 0 < K.right.card →
      (2 * 4 ^ K.right.card *
          (Delta * K.right.card + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hleave : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K →
      (∀ a : ↥K.left, (leaveGraph P).Adj K.center a.1) ∧
      (∀ b : ↥K.right, (leaveGraph P).Adj K.center b.1))
    (hdegree : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K →
      (∀ a : ↥K.left,
        (coveredGraph P).degree K.center +
          (coveredGraph P).degree a.1 ≤ degreeCutoff) ∧
      (∀ b : ↥K.right,
        (coveredGraph P).degree K.center +
          (coveredGraph P).degree b.1 ≤ degreeCutoff))
    (hroot : ∀ K : BipartiteLink V,
      IsResidualBipartition G P center K →
      (∀ (R : Finset (↥K.left × ↥K.right)) (a : ↥K.left),
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center a.1).card ≤ rootCutoff) ∧
      (∀ (R : Finset (↥K.left × ↥K.right)) (b : ↥K.right),
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center b.1).card ≤ rootCutoff))
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
    exact hKtyp.hasLinkCoverExtension_of_scalars Delta groupSize density
      candidate cutoff degreeCutoff rootCutoff familyCutoff hK.2.2
      hpositive hdensityLe (hmixingScalar K hK hpositive) hdegreeScalar
      (hdensityScalar K hK) hcandidateScalar sampleProbability hprob
      (hsampleScalar K hK hpositive) hPpacking hPavoid hfamily
      (hleave K hK).1 (hleave K hK).2 (hdegree K hK).1
      (hdegree K hK).2 (hroot K hK).1 (hroot K hK).2
      hdeletionScalar
  · have hempty : residualNeighbors G P center = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    refine ⟨emptyBipartiteLink center, ?_,
      emptyBipartiteLink_hasLinkCoverExtension F A P center hPpacking
        hPavoid⟩
    exact ⟨rfl, by simp [hempty], by simp⟩

end

end Erdos207
