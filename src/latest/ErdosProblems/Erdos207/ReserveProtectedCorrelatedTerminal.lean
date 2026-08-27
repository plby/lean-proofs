/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedCorrelatedRooted
import ErdosProblems.Erdos207.SupportedTerminalTypicalPipeline

/-!
# Terminal extraction from the correlated reserve-protected stage

The correlated preliminary/internal construction charges an internal triangle
together with its still-uncovered scheduled edge.  This file connects its
root-conditioned residual-link output to the terminal robust-link pipeline.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev ReserveProtectedCorrelatedRootedSample
    (Omega V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) :=
  Omega × (FiniteLaw.TimedState (GreedyStateOn V) n ×
    InternalEdgeGreedyStateOn V)

/-- The complete preliminary/internal addition in the right-associated
correlated sample space. -/
def reserveProtectedCorrelatedFinalTotal
    {Omega V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (z : ReserveProtectedCorrelatedRootedSample Omega V n) :
    TripleSystemOn V :=
  preliminaryInternalCombinedAdded
    (fun _ : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      reserveProtectedStagePreliminaryAdded z.1 z.2.1)
    (fun _ w ↦ rawResidualInternalAdded
      (fun y : Omega × FiniteLaw.TimedState (GreedyStateOn V) n ↦
        reserveProtectedStagePreliminaryAdded y.1 y.2)
      (z.1, z.2.1) w) z.2

/-- The structural family used by the residual-link and final-cover steps. -/
def reserveProtectedCorrelatedFinalFamily
    {Omega V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (z : ReserveProtectedCorrelatedRootedSample Omega V n) :
    TripleSystemOn V :=
  internalStageFamily ∅ ∅ (reserveProtectedCorrelatedFinalTotal z)
    z.2.2.chosen

/-- The sampled reserve augmented by all pairs missed by the combined
correlated addition. -/
def reserveProtectedCorrelatedFinalReserve
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (G : SimpleGraph V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell)
    (z : ReserveProtectedCorrelatedRootedSample Omega V n) :
    Finset (Sym2 V) :=
  preliminaryAugmentedReserve G (W.U i.succ)
    (reserveEdges G (W.U i.succ) (bits z.1))
    (reserveProtectedCorrelatedFinalTotal z)

/-- Canonical residual links of the correlated final state. -/
def reserveProtectedCorrelatedFinalLinks
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n q : ℕ}
    (W : Vortex V ell) (G : SimpleGraph V) (A B : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell)
    (z : ReserveProtectedCorrelatedRootedSample Omega V n) :
    {x : V // x ∉ W.U i.succ} → BipartiteLink V :=
  internalOutcomeResidualLinks (fun _ ↦ G) (W.U i.succ)
    (reserveProtectedCorrelatedFinalReserve W G bits i)
    (absorberErdosForbiddenConfigurationsOn q B) (fun _ ↦ A)
    (fun _ ↦ ∅) (fun _ ↦ ∅)
    reserveProtectedCorrelatedFinalTotal (fun z ↦ z.2.2.chosen) z

/-- The root-conditioned correlated stage, together with the terminal
typical-link scalar estimates, produces the exact outside packing. -/
theorem ReserveProtectedCorrelatedRootedResult.exists_ksssOutsidePacking
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level mid final : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A : TripleSystemOn V} {bits : Omega → Sym2 V → Bool}
    {i : Fin ell} {cutoff : ℕ} {p reserveDensity C b : ℝ≥0}
    {S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b}
    {T : ReserveProtectedRootedParameters L W level mid final F G A bits i
      cutoff p reserveDensity C b S}
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hresult : ReserveProtectedCorrelatedRootedResult L W level mid final F G
      A bits i cutoff p reserveDensity C b S T)
    (hF : F = absorberErdosForbiddenConfigurationsOn q B)
    (hki : level.val ≤ i.val)
    (hX : X = W.U i.succ)
    (hA : A ⊆ outsideAvailableTriangles H B)
    (hcover : CoversOriginalGraph
      (graphDifference (SimpleGraph.completeGraph V) H) G ∅ ∅)
    {eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W level G A S.pFinal eta xi h)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (m d degreeMax codegree loss : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (S.pFinal ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) *
      (S.pFinal ^ 2 * eta * (W.U i.succ).card) ≤ (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (S.pFinal ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ z : ReserveProtectedCorrelatedRootedSample Omega V S.n,
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ G (Classical.decRel G.Adj)
          (reserveProtectedCorrelatedFinalFamily z) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate hallCutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ z : ReserveProtectedCorrelatedRootedSample Omega V S.n,
      ∀ o : {x : V // x ∉ W.U i.succ},
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) (reserveProtectedCorrelatedFinalReserve W G bits i)
        (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        reserveProtectedCorrelatedFinalFamily d degreeMax codegree z
      0 < (K o).right.card → ∀ t : ℕ,
        hallCutoff < t → t ≤ (K o).right.card →
          (K o).right.card * (degreeMax + codegree * t) <
            t * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - hallCutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ Q ∈ F, Q.card ≤ familyCutoff)
    (hkappa : ∀ z : ReserveProtectedCorrelatedRootedSample Omega V S.n,
      ∀ e : DistinctPair V,
        HasExtensionBound
          (fun w : RootedThreatWitness V F e.1.1 e.1.2 ↦
            relativeRootedThreatRemainder
              (reserveProtectedCorrelatedFinalFamily z) w)
          (fun _ ↦ sigma) kappa)
    (hsmall : ∀ z : ReserveProtectedCorrelatedRootedSample Omega V S.n,
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) (reserveProtectedCorrelatedFinalReserve W G bits i)
        (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        reserveProtectedCorrelatedFinalFamily d degreeMax codegree z
      (Fintype.card
          (SimultaneousHallGroupIndex
            {x : V // x ∉ W.U i.succ} V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (sideMax : ℕ)
    (hstageTarget : (1 + xi) *
      (S.pFinal * (W.U i.castSucc).card) ≤ (sideMax : ℝ≥0))
    (hsideLoss : sideMax ≤ loss)
    (hdegreeCutoff : sideMax + sideMax ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ z : ReserveProtectedCorrelatedRootedSample Omega V S.n,
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) (reserveProtectedCorrelatedFinalReserve W G bits i)
        (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        reserveProtectedCorrelatedFinalFamily d degreeMax codegree z
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ W.U i.succ} V K ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkGood F
                (reserveProtectedCorrelatedFinalFamily z) (W.U i.succ)
                (outsideVertexEmbedding (W.U i.succ)) K
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ)
                    (reserveProtectedCorrelatedFinalReserve W G bits i)
                    (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
                    reserveProtectedCorrelatedFinalFamily d degreeMax
                    codegree z).1 o)
                (fun o ↦ o.2)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ)
                    (reserveProtectedCorrelatedFinalReserve W G bits i)
                    (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
                    reserveProtectedCorrelatedFinalFamily d degreeMax
                    codegree z).2.2.1 o)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ)
                    (reserveProtectedCorrelatedFinalReserve W G bits i)
                    (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
                    reserveProtectedCorrelatedFinalFamily d degreeMax
                    codegree z).2.2.2.1 o)
                (fun o ↦ linkAvailableRelation (K o) A)
                Delta rootCutoff) ≤ alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  subst F
  unfold ReserveProtectedCorrelatedRootedResult at hresult
  let F := absorberErdosForbiddenConfigurationsOn q B
  let Kpre := reserveProtectedStagePreliminaryKernel W F G A bits i S.n
    S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d
  let Mstar : Omega → FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := reserveProtectedStagePreliminaryAdded
  let P0 : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := fun z ↦ Mstar z.1 z.2
  let Aint : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := fun z ↦ pairSafeAvailable A (P0 z)
  let Gpre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      SimpleGraph V := fun _ ↦ G
  let bitsPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      Sym2 V → Bool := fun z ↦ bits z.1
  let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre S.D
  let K : Omega → FiniteLaw
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) := fun omega ↦
    (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi))
  let J := L.jointBind K
  let total : ReserveProtectedCorrelatedRootedSample Omega V S.n →
      TripleSystemOn V := reserveProtectedCorrelatedFinalTotal
  let reserve : ReserveProtectedCorrelatedRootedSample Omega V S.n →
      Finset (Sym2 V) := reserveProtectedCorrelatedFinalReserve W G bits i
  let RootGood : ReserveProtectedCorrelatedRootedSample Omega V S.n → Prop :=
    fun z ↦ RootedActiveCapsGood F (total z) S.R
  obtain ⟨hpos, _hreserve, hlinks, hstruct, _hlower⟩ := hresult
  let Lc := J.conditionOn RootGood hpos
  let Gfinal : ReserveProtectedCorrelatedRootedSample Omega V S.n →
      SimpleGraph V := fun _ ↦ G
  let Afinal : ReserveProtectedCorrelatedRootedSample Omega V S.n →
      TripleSystemOn V := fun _ ↦ A
  let Ifinal : ReserveProtectedCorrelatedRootedSample Omega V S.n →
      TripleSystemOn V := fun _ ↦ ∅
  let Dfinal : ReserveProtectedCorrelatedRootedSample Omega V S.n →
      TripleSystemOn V := fun _ ↦ ∅
  let Rfinal : ReserveProtectedCorrelatedRootedSample Omega V S.n →
      TripleSystemOn V := reserveProtectedCorrelatedFinalFamily
  let links : (z : ReserveProtectedCorrelatedRootedSample Omega V S.n) →
      {x : V // x ∉ W.U i.succ} → BipartiteLink V := fun z ↦
    internalOutcomeResidualLinks (fun _ ↦ G) (W.U i.succ)
      (fun z ↦ preliminaryAugmentedReserve G (W.U i.succ)
        (reserveEdges G (W.U i.succ) (bits z.1))
        (preliminaryInternalCombinedAdded
          (fun _ : FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
            reserveProtectedStagePreliminaryAdded z.1 z.2.1)
          (fun _ w ↦ rawResidualInternalAdded
            (fun y : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
              reserveProtectedStagePreliminaryAdded y.1 y.2)
            (z.1, z.2.1) w) z.2))
      F (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
      (fun z ↦ preliminaryInternalCombinedAdded
        (fun _ : FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
          reserveProtectedStagePreliminaryAdded z.1 z.2.1)
        (fun _ w ↦ rawResidualInternalAdded
          (fun y : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
            reserveProtectedStagePreliminaryAdded y.1 y.2)
          (z.1, z.2.1) w) z.2)
      (fun z ↦ z.2.2.chosen) z
  apply exists_ksssOutsidePacking_of_supportedIntermediateTypical i hki hX
    (law := Lc) (G := Gfinal) (A := Afinal) (I := Ifinal) (D := Dfinal)
    (R := Rfinal) (reserve := reserve) (Kold := links)
    (p := S.pFinal) (eta := eta) (xi := xi) (h := h)
    (q := q) (H := H) (X := X) (B := B)
    (m := m) (d := d) (degreeMax := degreeMax) (codegree := codegree)
    (loss := loss) (Delta := Delta) (groupSize := groupSize)
    (density := density) (candidate := candidate) (cutoff := hallCutoff)
    (degreeCutoff := degreeCutoff) (rootCutoff := rootCutoff)
    (familyCutoff := familyCutoff) (sigma := sigma) (kappa := kappa)
    (momentOrder := momentOrder) (sideMax := sideMax) (alpha := alpha)
    (hsigma := hsigma)
  · exact fun _ _ ↦ hA
  · intro z _hz
    simp [Ifinal, Dfinal]
  · intro z _hz
    simpa only [Gfinal, Ifinal, Dfinal] using hcover
  · exact fun _ _ ↦ htyp
  · exact fun z hz ↦ (hstruct z hz).1
  · exact fun z hz ↦ (hstruct z hz).2.1
  · exact fun _ _ ↦ hGsupp
  · simpa [Lc, J, Kpre, Mstar, P0, Aint, Gpre, bitsPre, K,
      Kint, total, reserve, RootGood, Gfinal, Afinal, Ifinal, Dfinal,
      Rfinal, links, F, reserveProtectedCorrelatedFinalTotal,
      reserveProtectedCorrelatedFinalFamily,
      reserveProtectedCorrelatedFinalReserve] using hlinks
  · intro z hz
    simpa [Ifinal, Dfinal, Rfinal, reserveProtectedCorrelatedFinalFamily,
      reserveProtectedCorrelatedFinalTotal] using (hstruct z hz).2.2.1
  · intro z hz
    simpa [Ifinal, Dfinal, Rfinal, reserveProtectedCorrelatedFinalFamily,
      reserveProtectedCorrelatedFinalTotal] using (hstruct z hz).2.2.2.1
  · exact hh
  · exact hlower
  · exact hupper
  · exact hcodegree
  · intro z _hz o
    exact hbisection z o
  · exact hdensityLe
  · intro z _hz o
    simpa only [Gfinal, Afinal, Ifinal, Dfinal, Rfinal, reserve] using
      hmixing z o
  · exact hdegreeScalar
  · exact hd
  · exact hdensityScalar
  · exact hcandidateScalar
  · exact hfamily
  · intro z _hz e
    simpa only [Ifinal, Dfinal, Rfinal, empty_union] using hkappa z e
  · intro z _hz
    simpa only [Gfinal, Afinal, Ifinal, Dfinal, Rfinal, reserve] using hsmall z
  · exact hstageTarget
  · exact hsideLoss
  · exact hdegreeCutoff
  · exact hdeletionScalar
  · intro z _hz
    simpa only [Gfinal, Afinal, Ifinal, Dfinal, Rfinal, reserve,
      empty_union] using hnormalizer z

end

end Erdos207
