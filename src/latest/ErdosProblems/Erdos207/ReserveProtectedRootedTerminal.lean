/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedRootedResidualLinks
import ErdosProblems.Erdos207.SupportedTerminalTypicalPipeline

/-!
# Terminal extraction from the reserve-protected rooted law

This file removes the dependent product bookkeeping from the last cover-down
step.  The hypotheses below are precisely the statewise scalar estimates for
the canonical residual links produced by the protected preliminary/internal
law; the conclusion is the exact KSSS outside packing.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev ReserveProtectedRootedSample
    (Omega V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) :=
  (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
    InternalEdgeGreedyStateOn V

def reserveProtectedRootedFinalFamily
    {Omega V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (z : ReserveProtectedRootedSample Omega V n) : TripleSystemOn V :=
  internalStageFamily ∅ ∅
    (reserveProtectedStagePreliminaryAdded z.1.1 z.1.2) z.2.chosen

def reserveProtectedRootedFinalReserve
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (G : SimpleGraph V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell)
    (z : ReserveProtectedRootedSample Omega V n) : Finset (Sym2 V) :=
  preliminaryAugmentedReserve G (W.U i.succ)
    (reserveEdges G (W.U i.succ) (bits z.1.1))
    (reserveProtectedStagePreliminaryAdded z.1.1 z.1.2)

def reserveProtectedRootedFinalLinks
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n q : ℕ}
    (W : Vortex V ell) (G : SimpleGraph V) (A : TripleSystemOn V)
    (B : TripleSystemOn V) (bits : Omega → Sym2 V → Bool)
    (i : Fin ell) (z : ReserveProtectedRootedSample Omega V n) :
    {x : V // x ∉ W.U i.succ} → BipartiteLink V :=
  internalOutcomeResidualLinks (fun _ ↦ G) (W.U i.succ)
    (reserveProtectedRootedFinalReserve W G bits i)
    (absorberErdosForbiddenConfigurationsOn q B) (fun _ ↦ A)
    (fun _ ↦ ∅) (fun _ ↦ ∅)
    (fun z ↦ reserveProtectedStagePreliminaryAdded z.1.1 z.1.2)
    (fun z ↦ z.2.chosen) z

theorem ReserveProtectedRootedResidualResult.exists_ksssOutsidePacking
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level final : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {i : Fin ell}
    {n Kpair Kglobal Kinc DeltaPre delta Icut Dcut dPre Dint Rroot q s : ℕ}
    {pFinal reserveDensity CFinal bFinal kappaRoot : ℝ≥0}
    {H : SimpleGraph V} {X : Finset V} {B : TripleSystemOn V}
    (hresult : ReserveProtectedRootedResidualResult L W final
      (absorberErdosForbiddenConfigurationsOn q B) G A bits i n
      Kpair Kglobal Kinc DeltaPre delta Icut Dcut dPre Dint Rroot q s
      pFinal reserveDensity CFinal bFinal kappaRoot)
    (hki : level.val ≤ i.val)
    (hX : X = W.U i.succ)
    (hA : A ⊆ outsideAvailableTriangles H B)
    (hcover : CoversOriginalGraph
      (graphDifference (SimpleGraph.completeGraph V) H) G ∅ ∅)
    {eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W level G A pFinal eta xi h)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (m d degreeMax codegree loss : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (pFinal ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) *
      (pFinal ^ 2 * eta * (W.U i.succ).card) ≤ (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (pFinal ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ z : ReserveProtectedRootedSample Omega V n,
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ G (Classical.decRel G.Adj)
          (reserveProtectedRootedFinalFamily z) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ z : ReserveProtectedRootedSample Omega V n,
      ∀ o : {x : V // x ∉ W.U i.succ},
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) (reserveProtectedRootedFinalReserve W G bits i)
        (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        reserveProtectedRootedFinalFamily d degreeMax codegree z
      0 < (K o).right.card → ∀ t : ℕ,
        cutoff < t → t ≤ (K o).right.card →
          (K o).right.card * (degreeMax + codegree * t) <
            t * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ absorberErdosForbiddenConfigurationsOn q B,
      C.card ≤ familyCutoff)
    (hkappa : ∀ z : ReserveProtectedRootedSample Omega V n,
      ∀ e : DistinctPair V,
        HasExtensionBound
          (fun w : RootedThreatWitness V
              (absorberErdosForbiddenConfigurationsOn q B) e.1.1 e.1.2 ↦
            relativeRootedThreatRemainder
              (reserveProtectedRootedFinalFamily z) w)
          (fun _ ↦ sigma) kappa)
    (hsmall : ∀ z : ReserveProtectedRootedSample Omega V n,
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) (reserveProtectedRootedFinalReserve W G bits i)
        (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        reserveProtectedRootedFinalFamily d degreeMax codegree z
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
      (pFinal * (W.U i.castSucc).card) ≤ (sideMax : ℝ≥0))
    (hsideLoss : sideMax ≤ loss)
    (hdegreeCutoff : sideMax + sideMax ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ z : ReserveProtectedRootedSample Omega V n,
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) (reserveProtectedRootedFinalReserve W G bits i)
        (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        reserveProtectedRootedFinalFamily d degreeMax codegree z
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ W.U i.succ} V K ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkGood
                (absorberErdosForbiddenConfigurationsOn q B)
                (reserveProtectedRootedFinalFamily z) (W.U i.succ)
                (outsideVertexEmbedding (W.U i.succ)) K
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ)
                    (reserveProtectedRootedFinalReserve W G bits i)
                    (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
                    reserveProtectedRootedFinalFamily d degreeMax codegree z).1 o)
                (fun o ↦ o.2)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ)
                    (reserveProtectedRootedFinalReserve W G bits i)
                    (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
                    reserveProtectedRootedFinalFamily d degreeMax codegree z).2.2.1 o)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ)
                    (reserveProtectedRootedFinalReserve W G bits i)
                    (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
                    reserveProtectedRootedFinalFamily d degreeMax codegree z).2.2.2.1 o)
                (fun o ↦ linkAvailableRelation (K o) A)
                Delta rootCutoff) ≤ alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  unfold ReserveProtectedRootedResidualResult at hresult
  let Kpre := reserveProtectedStagePreliminaryKernel W
    (absorberErdosForbiddenConfigurationsOn q B) G A bits i n
    Kpair Kglobal Kinc DeltaPre delta Icut Dcut dPre
  let Mstar : Omega → FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := reserveProtectedStagePreliminaryAdded
  let LP := L.jointBind Kpre
  let P0 : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ ∅ ∪ Mstar z.1 z.2
  let Aint : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ pairSafeAvailable A (P0 z)
  let Gpre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      SimpleGraph V := fun _ ↦ G
  let bitsPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      Sym2 V → Bool := fun z ↦ bits z.1
  let Kint := rawResidualInternalKernel W i
    (absorberErdosForbiddenConfigurationsOn q B) Gpre Aint P0 bitsPre Dint
  let J := LP.jointBind Kint
  let initialPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := jointInitial (fun _ : Omega ↦ ∅)
  let laterPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := jointLater (fun _ : Omega ↦ ∅) Mstar
  let RootGood : ReserveProtectedRootedSample Omega V n → Prop := fun z ↦
    RootedActiveCapsGood (absorberErdosForbiddenConfigurationsOn q B)
      (jointInitial initialPre z ∪
        jointLater laterPre (rawResidualInternalAdded P0) z) Rroot
  obtain ⟨hpos, _hreserve, hlinks, hstruct, _hlower⟩ := hresult
  let Lc := J.conditionOn RootGood hpos
  let Gfinal : ReserveProtectedRootedSample Omega V n → SimpleGraph V :=
    fun _ ↦ G
  let Afinal : ReserveProtectedRootedSample Omega V n → TripleSystemOn V :=
    fun _ ↦ A
  let Ifinal : ReserveProtectedRootedSample Omega V n → TripleSystemOn V :=
    fun _ ↦ ∅
  let Dfinal : ReserveProtectedRootedSample Omega V n → TripleSystemOn V :=
    fun _ ↦ ∅
  let Rfinal : ReserveProtectedRootedSample Omega V n → TripleSystemOn V :=
    reserveProtectedRootedFinalFamily
  let reserveFinal : ReserveProtectedRootedSample Omega V n →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ)
      (reserveEdges G (W.U i.succ) (bits z.1.1))
      (reserveProtectedStagePreliminaryAdded z.1.1 z.1.2)
  have hreserveFinal : reserveFinal =
      reserveProtectedRootedFinalReserve W G bits i := by
    rfl
  let links : (z : ReserveProtectedRootedSample Omega V n) →
      {x : V // x ∉ W.U i.succ} → BipartiteLink V :=
    internalOutcomeResidualLinks (fun _ ↦ G) (W.U i.succ) reserveFinal
      (absorberErdosForbiddenConfigurationsOn q B) (fun _ ↦ A)
      (fun _ ↦ ∅) (fun _ ↦ ∅)
      (fun z ↦ reserveProtectedStagePreliminaryAdded z.1.1 z.1.2)
      (fun z ↦ z.2.chosen)
  apply exists_ksssOutsidePacking_of_supportedIntermediateTypical i hki hX
    (law := Lc) (G := Gfinal) (A := Afinal) (I := Ifinal) (D := Dfinal)
    (R := Rfinal) (reserve := reserveFinal) (Kold := links)
    (p := pFinal) (eta := eta) (xi := xi) (h := h)
    (q := q) (H := H) (X := X) (B := B)
    (m := m) (d := d) (degreeMax := degreeMax) (codegree := codegree)
    (loss := loss) (Delta := Delta) (groupSize := groupSize)
    (density := density) (candidate := candidate) (cutoff := cutoff)
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
  · simpa only [Lc, J, LP, Kint, Kpre, Mstar, P0, Aint, Gpre, bitsPre,
      initialPre, laterPre, RootGood, Gfinal, Afinal, Ifinal, Dfinal,
      Rfinal, reserveFinal, links, reserveProtectedRootedFinalFamily,
      reserveProtectedRootedFinalReserve,
      reserveProtectedRootedFinalLinks] using hlinks
  · exact fun z hz ↦ (hstruct z hz).2.2.1
  · exact fun z hz ↦ (hstruct z hz).2.2.2.1
  · exact hh
  · exact hlower
  · exact hupper
  · exact hcodegree
  · intro z _hz o
    exact hbisection z o
  · exact hdensityLe
  · intro z _hz o
    simp only [Gfinal, Afinal, Ifinal, Dfinal, Rfinal]
    rw [hreserveFinal]
    exact hmixing z o
  · exact hdegreeScalar
  · exact hd
  · exact hdensityScalar
  · exact hcandidateScalar
  · exact hfamily
  · intro z _hz e
    simpa only [Ifinal, Dfinal, Rfinal, empty_union] using hkappa z e
  · intro z _hz
    simp only [Gfinal, Afinal, Ifinal, Dfinal, Rfinal]
    rw [hreserveFinal]
    exact hsmall z
  · exact hstageTarget
  · exact hsideLoss
  · exact hdegreeCutoff
  · exact hdeletionScalar
  · intro z _hz
    simp only [Gfinal, Afinal, Ifinal, Dfinal, Rfinal, empty_union]
    rw [hreserveFinal]
    exact hnormalizer z

end

end Erdos207
