/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyPreliminaryInternalStage
import ErdosProblems.Erdos207.LocalizedInternalStageLoss
import ErdosProblems.Erdos207.RawInternalResidualLinks
import ErdosProblems.Erdos207.SharpSupportedTerminalResidualReady

/-!
# Terminal extraction after an outer-only raw internal stage

The outer-only preliminary family contributes no covered neighbour in the
terminal vortex set.  Consequently the localized residual-link loss is the
scheduled internal incidence, rather than the full degree of the preceding
graph.  This is the quantitative terminal interface used by the one-stage
construction.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A raw internal law whose preliminary family is outer-only can be rooted-
conditioned, re-bisected into typical residual links, and completed by the
robust simultaneous link cover. -/
theorem exists_ksssOutsidePacking_of_outerOnlyRawStage
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level final : Fin (ell + 1)} {i : Fin ell}
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {G : SimpleGraph V}
    {A : TripleSystemOn V} {M : Omega → TripleSystemOn V}
    {initial later : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {Dint Rroot : ℕ}
    {pFinal reserveDensity CFinal bFinal : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed
      (L.jointBind (rawResidualInternalKernel W i
        (absorberErdosForbiddenConfigurationsOn q B)
        (fun _ ↦ G) (fun omega ↦ pairSafeAvailable A (M omega))
        M bits Dint)) W final
      (jointInitial initial)
      (jointLater later (rawResidualInternalAdded M))
      (fun z ↦ preliminaryAugmentedReserve G (W.U i.succ) ∅ (M z.1))
      pFinal reserveDensity CFinal bFinal)
    (hinitialLater : ∀ omega, initial omega ∪ later omega = M omega)
    (hraw : (L.jointBind (rawResidualInternalKernel W i
      (absorberErdosForbiddenConfigurationsOn q B)
      (fun _ ↦ G) (fun omega ↦ pairSafeAvailable A (M omega))
      M bits Dint)).SupportedOn (fun z ↦
        RawResidualInternalOutcomeGood W i
          (absorberErdosForbiddenConfigurationsOn q B)
          (fun _ ↦ G) (fun omega ↦ pairSafeAvailable A (M omega))
          M bits Dint Rroot z.1 z.2))
    (hpre : (L.jointBind (rawResidualInternalKernel W i
      (absorberErdosForbiddenConfigurationsOn q B)
      (fun _ ↦ G) (fun omega ↦ pairSafeAvailable A (M omega))
      M bits Dint)).SupportedOn (fun z ↦
        M z.1 ⊆ A ∧ IsPackingOn (M z.1) ∧
          AvoidsForbidden (M z.1)
            (absorberErdosForbiddenConfigurationsOn q B) ∧
          TrianglesDisjointFrom (W.U i.succ) (M z.1) ∧
          ∀ v : V,
            (scheduledEdgesAt
              (preliminaryResidualInternalEdges G (W.U i.succ) (M z.1))
              v).card ≤ Dint))
    (hCFinal : 1 ≤ CFinal) (s : ℕ)
    (hfamilyRoot : ∀ S ∈ absorberErdosForbiddenConfigurationsOn q B,
      S.card ≤ q)
    (hbRoot : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) →
      bFinal ≤ setWeight (masterUnionTriangleWeight W final pFinal) T)
    (kappaRoot : ℝ≥0)
    (hkappaRoot : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W final pFinal) kappaRoot)
    (htailRoot : strongRootedTail V CFinal kappaRoot Rroot q s < 1)
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (∅ : TripleSystemOn V))
    (hA : A ⊆ outsideAvailableTriangles H B)
    (hcover : CoversOriginalGraph
      (graphDifference (SimpleGraph.completeGraph V) H) G ∅ ∅)
    {eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W level G A pFinal eta xi h)
    (hki : level.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (m d degreeMax codegree : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + Dint + 1 : ℝ≥0) ≤
      (1 - xi) * (pFinal ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) *
      (pFinal ^ 2 * eta * (W.U i.succ).card) ≤ (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (pFinal ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ G (Classical.decRel G.Adj)
          (internalStageFamily ∅ ∅ (M z.1) z.2.chosen) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ absorberErdosForbiddenConfigurationsOn q B,
      C.card ≤ familyCutoff)
    (hkappa : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      ∀ e : DistinctPair V,
        HasExtensionBound
          (fun w : RootedThreatWitness V
              (absorberErdosForbiddenConfigurationsOn q B) e.1.1 e.1.2 ↦
            relativeRootedThreatRemainder
              (internalStageFamily ∅ ∅ (M z.1) z.2.chosen) w)
          (fun _ ↦ sigma) kappa)
    (hsmall : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      let reserve := fun z : Omega × InternalEdgeGreedyStateOn V ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (M z.1)
      let R := fun z : Omega × InternalEdgeGreedyStateOn V ↦
        internalStageFamily ∅ ∅ (M z.1) z.2.chosen
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) reserve (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        R d degreeMax codegree z
      (∑ o : {x : V // x ∉ W.U i.succ},
        ∑ obstruction : OrientedSmallHallObstruction
            ↑(K o).left ↑(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates
                (linkAvailableRelation (K o) A) obstruction).card /
            (1 / 2 : ℝ≥0) ^
              (Delta * orientedSmallHallSize obstruction)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (sideMax : ℕ)
    (hstageDegree : ∀ v : V, (G.neighborSet v).ncard ≤ sideMax)
    (hdegreeCutoff : sideMax + sideMax ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      let reserve := fun z : Omega × InternalEdgeGreedyStateOn V ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (M z.1)
      let R := fun z : Omega × InternalEdgeGreedyStateOn V ↦
        internalStageFamily ∅ ∅ (M z.1) z.2.chosen
      let K := supportedReserveTypicalResidualLinks (fun _ ↦ G)
        (W.U i.succ) reserve (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
        R d degreeMax codegree z
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ W.U i.succ} V K ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkGood
                (absorberErdosForbiddenConfigurationsOn q B)
                (R z) (W.U i.succ)
                (outsideVertexEmbedding (W.U i.succ)) K
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ) reserve (fun _ ↦ A) (fun _ ↦ ∅)
                    (fun _ ↦ ∅) R d degreeMax codegree z).1 o)
                (fun o ↦ o.2)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ) reserve (fun _ ↦ A) (fun _ ↦ ∅)
                    (fun _ ↦ ∅) R d degreeMax codegree z).2.2.1 o)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global (fun _ ↦ G)
                    (W.U i.succ) reserve (fun _ ↦ A) (fun _ ↦ ∅)
                    (fun _ ↦ ∅) R d degreeMax codegree z).2.2.2.1 o)
                (fun o ↦ linkAvailableRelation (K o) A)
                Delta rootCutoff) ≤ alpha)
    (hX : X = W.U i.succ) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let Kint := rawResidualInternalKernel W i F (fun _ ↦ G)
    (fun omega ↦ pairSafeAvailable A (M omega)) M bits Dint
  let J := L.jointBind Kint
  let reserve0 : Omega → Finset (Sym2 V) := fun omega ↦
    preliminaryAugmentedReserve G (W.U i.succ) ∅ (M omega)
  have hroot := hstrong.conditionOn_rawResidualInternal_rootedSuccess
    (G := fun _ ↦ G) (A := fun omega ↦ pairSafeAvailable A (M omega))
    (P0 := M) (bits := bits) (initial := initial) (later := later)
    (reserve := reserve0) i (fun _ ↦ True)
    (by
      intro z hz
      exact ⟨trivial, hraw z (by simpa only [J, Kint, F] using hz)⟩)
    (fun omega _ ↦ hinitialLater omega) hCFinal hfamilyRoot hbRoot
    kappaRoot hkappaRoot htailRoot
  obtain ⟨hpos, hstrongC, hcomplete, _hlower⟩ := hroot
  let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
    RootedActiveCapsGood F
      (jointInitial initial z ∪
        jointLater later (rawResidualInternalAdded M) z) Rroot
  let Lc := J.conditionOn RootGood hpos
  have hpreC : Lc.SupportedOn (fun z ↦
      M z.1 ⊆ A ∧ IsPackingOn (M z.1) ∧ AvoidsForbidden (M z.1) F ∧
        TrianglesDisjointFrom (W.U i.succ) (M z.1) ∧
        ∀ v : V,
          (scheduledEdgesAt
            (preliminaryResidualInternalEdges G (W.U i.succ) (M z.1))
            v).card ≤ Dint) := by
    simpa only [Lc, J, Kint, F] using hpre.conditionOn hpos
  have hrawC : Lc.SupportedOn (fun z ↦
      RawResidualInternalOutcomeGood W i F (fun _ ↦ G)
        (fun omega ↦ pairSafeAvailable A (M omega)) M bits Dint Rroot
        z.1 z.2) := by
    simpa only [Lc, J, Kint, F] using hraw.conditionOn hpos
  let Gf : Omega × InternalEdgeGreedyStateOn V → SimpleGraph V := fun _ ↦ G
  let Af : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ A
  let If : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ ∅
  let Df : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ ∅
  let Mf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦ M z.1
  let Qf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦ z.2.chosen
  let Rf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦
    internalStageFamily (If z) (Df z) (Mf z) (Qf z)
  let reservef : Omega × InternalEdgeGreedyStateOn V → Finset (Sym2 V) :=
    fun z ↦ preliminaryAugmentedReserve G (W.U i.succ) ∅ (M z.1)
  let links := internalOutcomeResidualLinks Gf (W.U i.succ) reservef F
    Af If Df Mf Qf
  have hbase : Lc.SupportedOn fun z ↦
      (∀ v, Even ((neighborsIn (Gf z) univ v).card)) ∧
      Gf z ≤ leaveGraph (If z ∪ Df z) ∧
      ConsistsOfTriangles (Gf z) (Af z) ∧ Mf z ⊆ Af z ∧
      Disjoint (If z) (Df z ∪ Mf z) ∧ IsPackingOn (Mf z) := by
    intro z hz
    exact ⟨heven, by simpa [Gf, If, Df] using hGleave, htri,
      (hpreC z hz).1, by simp [If], (hpreC z hz).2.1⟩
  have hinternal : Lc.SupportedOn fun z ↦
      GreedyReachable F (Mf z) (Qf z) ∧
      Qf z ⊆ Mf z ∪ Af z ∧
      (Qf z \ Mf z).card ≤ (internalOuterEdges (Gf z) (W.U i.succ)).card ∧
      ∀ e ∈ internalOuterEdges (Gf z) (W.U i.succ),
        (coveredGraph (Qf z)).Adj e.out.1 e.out.2 := by
    intro z hz
    have hc := hcomplete z hz
    refine ⟨hc.2.1, ?_, hc.2.2.2.1, hc.2.2.2.2.1⟩
    intro T hT
    rcases mem_union.mp (hc.2.2.1 hT) with hTM | hTsafe
    · exact mem_union_left A hTM
    · exact mem_union_right (M z.1)
        (pairSafeAvailable_subset_left A (M z.1) hTsafe)
  have hlinks : Lc.SupportedOn fun z ↦
      IsIntermediateLinkState (Gf z) (W.U i.succ) (Af z) (If z) (Df z)
          (Rf z) (links z) ∧
        (∀ o, (links z o).center = outsideVertexEmbedding (W.U i.succ) o) ∧
        (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
        (∀ o, (links z o).left ⊆ W.U i.succ) ∧
        (∀ o, (links z o).right ⊆ W.U i.succ) ∧
        (∀ o, (links z o).SpokesIn (reservef z)) := by
    have hs := hbase.rawPreliminaryInternalResidualLinks
      (U := W.U i.succ) (sampled := fun _ ↦ ∅) (F := F)
      (A := Af) (I := If) (D := Df) (Mstar := Mf) (P0 := Mf) (Q := Qf)
      (fun _ ↦ by simp [If, Df]) hinternal
    simpa only [Gf, reservef, Rf, links] using hs
  have hcovered : Lc.SupportedOn fun z ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((coveredGraph (Rf z)).neighborFinset o.1 ∩ W.U i.succ).card ≤ Dint := by
    intro z hz o
    have hp := hpreC z hz
    have hr := hrawC z hz
    have hreach := hinternal z hz |>.1
    apply card_coveredNeighborsIn_internalStageFamily_le_scheduledIncidence
      (I := If z) (D := Df z) (Mstar := Mf z) (P0 := Mf z) (Q := Qf z)
      (E := preliminaryResidualInternalEdges G (W.U i.succ) (M z.1))
    · simp [If, Df, Mf]
    · exact hp.2.2.2.1
    · exact hreach.initial_subset
    · exact hreach.isPacking hp.2.1
    · intro e he
      exact (mem_internalOuterEdges_iff.mp
        (preliminaryResidualInternalEdges_subset_internalOuterEdges
          G (W.U i.succ) (M z.1) he)).2
    · simpa only [F, Gf, Af, Mf, Qf] using hr.2.2.1
    · simpa only [Gf, Mf] using hp.2.2.2.2
    · exact o.2
  have htypSupport : Lc.SupportedOn fun _ ↦
      IsIterationTypical W level G A pFinal eta xi h := fun _ _ ↦ htyp
  have hready :=
    FiniteLaw.SupportedOn.reserveSupportedTypicalResidualLinks_of_typical_localized
      i hki (W.U i.succ) rfl reservef links
      htypSupport (fun _ _ ↦ htri) (fun _ _ ↦ hGsupp)
      hlinks m d degreeMax codegree Dint hcovered hh hlower hupper hcodegree
      (by
        intro z _hz o
        simpa only [Gf, Rf] using hbisection z o)
  have hpacking : Lc.SupportedOn fun z ↦
      IsPackingOn (If z ∪ (Df z ∪ Rf z)) := by
    intro z hz
    have hreach := hinternal z hz |>.1
    have hRsub : Rf z ⊆ Qf z := by
      intro T hT
      rcases mem_union.mp hT with hTM | hTnew
      · exact hreach.initial_subset (by simpa [If, Df, Mf] using hTM)
      · exact (mem_sdiff.mp hTnew).1
    exact (hreach.isPacking (hpreC z hz).2.1).mono (by
      simpa [If, Df] using hRsub)
  have havoid : Lc.SupportedOn fun z ↦
      AvoidsForbidden (If z ∪ (Df z ∪ Rf z)) F := by
    intro z hz
    have hreach := hinternal z hz |>.1
    have hRsub : Rf z ⊆ Qf z := by
      intro T hT
      rcases mem_union.mp hT with hTM | hTnew
      · exact hreach.initial_subset (by simpa [If, Df, Mf] using hTM)
      · exact (mem_sdiff.mp hTnew).1
    exact (hreach.avoidsForbidden (hpreC z hz).2.2.1).mono (by
      simpa [If, Df] using hRsub)
  apply exists_ksssOutsidePacking_of_supportedResidualLinksReady_sharp i
    (law := Lc) (W := W) (G := Gf) (A := Af) (I := If) (D := Df)
    (R := Rf) (reserve := reservef) (q := q) (H := H) (X := X) (B := B)
    (Delta := Delta) (degreeCutoff := degreeCutoff) (rootCutoff := rootCutoff)
    (familyCutoff := familyCutoff) (sigma := sigma) (kappa := kappa)
    (momentOrder := momentOrder) (sideMax := sideMax) (alpha := alpha)
    d degreeMax codegree hX
  · exact fun _ _ ↦ hA
  · intro z _hz
    simp [If, Df]
  · exact fun _ _ ↦ hcover
  · exact hready
  · exact fun _ _ ↦ htri
  · exact fun _ _ ↦ by simpa [If, Df] using hGleave
  · exact hfamily
  · intro z _hz e
    simpa only [If, Df, Rf, F, empty_union] using hkappa z e
  · intro z _hz
    simpa only [Gf, Af, If, Df, Rf, reservef] using hsmall z
  · exact hpacking
  · exact havoid
  · exact fun _ _ v ↦ hstageDegree v
  · exact hdegreeCutoff
  · exact hdeletionScalar
  · intro z _hz
    simpa only [Gf, Af, If, Df, Rf, reservef, empty_union] using hnormalizer z

end

end Erdos207
