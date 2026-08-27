/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationDynamicMasterLinkStage
import ErdosProblems.Erdos207.IterationChosenLinkCoverGood

/-!
# Dynamic master link stage with probabilistic rooted control

This is the corrected KSSS master-link interface.  Every center receives a
fresh residual bisection, and its Bernoulli link reservoir is selected to
satisfy robust Hall and the rooted-threat cutoff on the same outcome.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsIterationTypical.exists_masterCoverStep_of_dynamic_link_scalars_good
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {F : ForbiddenFamilyOn V} {A I D R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (heven : ∀ v, Even (G.degree v))
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hRcover : ∀ u v : V, G.Adj u v →
      u ∉ W.U i.succ → v ∉ W.U i.succ →
      (coveredGraph R).Adj u v)
    (hpreDisjoint : Disjoint I (D ∪ R))
    (hprePacking : IsPackingOn (I ∪ (D ∪ R)))
    (hpreAvoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (m d Dmax codegree loss : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (Dmax : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤
        (codegree : ℝ≥0))
    (hcovered : ∀ (P : TripleSystemOn V),
      IsDynamicLinkState F A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
        (coveredGraph P).degree o.1 ≤ loss)
    (hbisection : ∀ (P : TripleSystemOn V),
      IsDynamicLinkState F A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((residualNeighbors G P o.1).card : ℝ≥0) *
          (2 * (2 : ℝ≥0) ^ d *
            (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixingScalar : ∀ (P : TripleSystemOn V),
      IsDynamicLinkState F A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ∀ K : BipartiteLink V, IsResidualBipartition G P o.1 K →
        0 < K.right.card →
      ∀ s : ℕ, cutoff < s → s ≤ K.right.card →
        K.right.card * (Dmax + codegree * s) <
          s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdTwo : 2 ≤ d)
    (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (epsilon : ℝ≥0)
    (hrootBad : ∀ (P : TripleSystemOn V),
      IsDynamicLinkState F A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ∀ K : BipartiteLink V, IsResidualBipartition G P o.1 K →
        0 < K.right.card →
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
    (hsampleScalar : ∀ (P : TripleSystemOn V),
      IsDynamicLinkState F A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ∀ K : BipartiteLink V, IsResidualBipartition G P o.1 K →
        0 < K.right.card →
        epsilon + (2 * 4 ^ K.right.card *
            (Delta * K.right.card + 1) : ℝ≥0) *
          (1 - sampleProbability) ^ groupSize < 1)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hdegree : ∀ (P : TripleSystemOn V),
      IsDynamicLinkState F A I D R P →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ∀ K : BipartiteLink V, IsResidualBipartition G P o.1 K →
      (∀ a : ↥K.left,
        (coveredGraph P).degree K.center +
          (coveredGraph P).degree a.1 ≤ degreeCutoff) ∧
      (∀ b : ↥K.right,
        (coveredGraph P).degree K.center +
          (coveredGraph P).degree b.1 ≤ degreeCutoff))
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    ∃ M : TripleSystemOn V,
      IsMasterCoverStep F G (W.U i.succ) A I D M := by
  apply exists_masterCoverStep_of_dynamic_crossingLinkExtensions hold
    hRselected hpreDisjoint hprePacking hpreAvoid
  intro P hP₀P hPsub hPpacking hPavoid o
  have hstate : IsDynamicLinkState F A I D R P :=
    ⟨hP₀P, hPsub, hPpacking, hPavoid⟩
  have hRP : R ⊆ P := by
    intro T hTR
    exact hP₀P (mem_union_right I (mem_union_right D hTR))
  have hresInner : residualNeighbors G P o.1 ⊆ W.U i.succ :=
    residualNeighbors_subset_of_internal_cover hRP hRcover o.2
  have hresEven : Even (residualNeighbors G P o.1).card :=
    residualNeighbors_even_of_dynamic_state heven htri hold hRselected
      hPsub hPpacking o.1
  exact htyp.exists_chosenResidualLinkCover_good_of_supported htri i hki
    hGsupp o.1 o.2 hresInner hresEven m d Dmax codegree loss
    (hcovered P hstate o) hh hlower hupper hcodegree
    (hbisection P hstate o) Delta groupSize density candidate cutoff
    degreeCutoff rootCutoff familyCutoff hdensityLe
    (fun K hK hpos ↦ hmixingScalar P hstate o K hK hpos)
    hdegreeScalar hdTwo hdensityScalar
    hcandidateScalar sampleProbability hprob epsilon
    (fun K hK hpos ↦ hrootBad P hstate o K hK hpos)
    (fun K hK hpos ↦ hsampleScalar P hstate o K hK hpos)
    hPpacking hPavoid hfamily
    (fun K hK ↦ hdegree P hstate o K hK) hdeletionScalar

end

end Erdos207
