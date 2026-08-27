/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedRootedConditioning
import ErdosProblems.Erdos207.RawInternalResidualLinks

/-!
# Residual links after the reserve-protected rooted stage

This file packages the conditioned preliminary/internal law into the exact
intermediate-link and structural support consumed by the terminal KSSS
pipeline.  The ambient available family is retained: the pair-safe family is
used only by the internal kernel, and its support is widened back to the
ambient family when the canonical residual links are constructed.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ReserveProtectedRootedResidualResult
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (final : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell) (n : ℕ)
    (Kpair Kglobal Kinc Delta delta Icut Dcut d D R q s : ℕ)
    (pFinal reserveDensityMid CFinal bFinal kappa : ℝ≥0) : Prop :=
  let Kpre := reserveProtectedStagePreliminaryKernel W F G A bits i n
    Kpair Kglobal Kinc Delta delta Icut Dcut d
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
  let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre D
  let J := LP.jointBind Kint
  let initialPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := jointInitial (fun _ : Omega ↦ ∅)
  let laterPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := jointLater (fun _ : Omega ↦ ∅) Mstar
  let reservePre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ)
      (reserveEdges G (W.U i.succ) (bits z.1)) (Mstar z.1 z.2)
  let Good : Omega × FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    reserveProtectedStagePreliminaryGood L Kpre
  let RootGood :
      (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → Prop := fun z ↦
    RootedActiveCapsGood F
      (jointInitial initialPre z ∪
        jointLater laterPre (rawResidualInternalAdded P0) z) R
  ∃ hpos : 0 < J.probability RootGood,
    let Lc := J.conditionOn RootGood hpos
    let Ifinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ ∅
    let Dfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ ∅
    let Mfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦
      Mstar z.1.1 z.1.2
    let Qfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦ z.2.chosen
    let Rfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦
      internalStageFamily (Ifinal z) (Dfinal z) (Mfinal z) (Qfinal z)
    let Gfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → SimpleGraph V := fun _ ↦ G
    let Afinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ A
    let sampledFinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) n) ×
        InternalEdgeGreedyStateOn V → Finset (Sym2 V) := fun z ↦
      reserveEdges G (W.U i.succ) (bits z.1.1)
    let links := internalOutcomeResidualLinks Gfinal (W.U i.succ)
      (fun z ↦ preliminaryAugmentedReserve (Gfinal z) (W.U i.succ)
        (sampledFinal z) (Mfinal z)) F Afinal Ifinal Dfinal Mfinal Qfinal
    IsReserveStronglyWellDistributed Lc W final
        (jointInitial initialPre)
        (jointLater laterPre (rawResidualInternalAdded P0))
        (fun z ↦ reservePre z.1) pFinal reserveDensityMid
        ((2 * CFinal) /
          (1 - strongRootedTail V (2 * CFinal) kappa R q s)) bFinal ∧
      Lc.SupportedOn (fun z ↦
        IsIntermediateLinkState (Gfinal z) (W.U i.succ) (Afinal z)
            (Ifinal z) (Dfinal z) (Rfinal z) (links z) ∧
          (∀ o, (links z o).center = outsideVertexEmbedding (W.U i.succ) o) ∧
          (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
          (∀ o, (links z o).left ⊆ W.U i.succ) ∧
          (∀ o, (links z o).right ⊆ W.U i.succ) ∧
          (∀ o, (links z o).SpokesIn
            (preliminaryAugmentedReserve (Gfinal z) (W.U i.succ)
              (sampledFinal z) (Mfinal z)))) ∧
      Lc.SupportedOn (fun z ↦
        ConsistsOfTriangles (Gfinal z) (Afinal z) ∧
          Gfinal z ≤ leaveGraph (Ifinal z ∪ Dfinal z) ∧
          IsPackingOn (Ifinal z ∪ (Dfinal z ∪ Rfinal z)) ∧
          AvoidsForbidden (Ifinal z ∪ (Dfinal z ∪ Rfinal z)) F ∧
          RootedActiveCapsGood F (Qfinal z) R) ∧
      1 - strongRootedTail V (2 * CFinal) kappa R q s ≤
        J.probability RootGood

theorem ReserveProtectedRootedConditioningResult.residualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level mid final : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {i : Fin ell} {cutoff : ℕ}
    {p reserveDensity C b : ℝ≥0}
    {S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b}
    {T : ReserveProtectedRootedParameters L W level mid final F G A bits i
      cutoff p reserveDensity C b S}
    (hrooted : ReserveProtectedRootedConditioningResult L W final F G A bits
      i S.n S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d S.D
      S.R S.q T.s S.pFinal S.reserveDensityMid S.CFinal S.bFinal T.kappa)
    (hstageGood : L.SupportedOn fun omega ↦
      ReserveProtectedStageGood W i G A ∅ cutoff (bits omega))
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (htri : ConsistsOfTriangles G A) :
    ReserveProtectedRootedResidualResult L W final F G A bits i S.n
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d S.D S.R
      S.q T.s S.pFinal S.reserveDensityMid S.CFinal S.bFinal T.kappa := by
  unfold ReserveProtectedRootedConditioningResult at hrooted
  unfold ReserveProtectedRootedResidualResult
  let Kpre := reserveProtectedStagePreliminaryKernel W F G A bits i S.n
    S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d
  let Mstar : Omega → FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := reserveProtectedStagePreliminaryAdded
  let LP := L.jointBind Kpre
  let P0 : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := fun z ↦ ∅ ∪ Mstar z.1 z.2
  let Aint : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := fun z ↦ pairSafeAvailable A (P0 z)
  let Gpre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      SimpleGraph V := fun _ ↦ G
  let bitsPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      Sym2 V → Bool := fun z ↦ bits z.1
  let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre S.D
  let J := LP.jointBind Kint
  let initialPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := jointInitial (fun _ : Omega ↦ ∅)
  let laterPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := jointLater (fun _ : Omega ↦ ∅) Mstar
  let reservePre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ)
      (reserveEdges G (W.U i.succ) (bits z.1)) (Mstar z.1 z.2)
  let Good : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n → Prop :=
    reserveProtectedStagePreliminaryGood L Kpre
  let RootGood :
      (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
        InternalEdgeGreedyStateOn V → Prop := fun z ↦
    RootedActiveCapsGood F
      (jointInitial initialPre z ∪
        jointLater laterPre (rawResidualInternalAdded P0) z) S.R
  obtain ⟨hpos, hreserve, hsupp, hlower⟩ := hrooted
  refine ⟨hpos, ?_⟩
  let Lc := J.conditionOn RootGood hpos
  let Ifinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ ∅
  let Dfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ ∅
  let Mfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦
    Mstar z.1.1 z.1.2
  let Qfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦ z.2.chosen
  let Rfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → TripleSystemOn V := fun z ↦
    internalStageFamily (Ifinal z) (Dfinal z) (Mfinal z) (Qfinal z)
  let Gfinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → SimpleGraph V := fun _ ↦ G
  let Afinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → TripleSystemOn V := fun _ ↦ A
  let sampledFinal : (Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n) ×
      InternalEdgeGreedyStateOn V → Finset (Sym2 V) := fun z ↦
    reserveEdges G (W.U i.succ) (bits z.1.1)
  let links := internalOutcomeResidualLinks Gfinal (W.U i.succ)
    (fun z ↦ preliminaryAugmentedReserve (Gfinal z) (W.U i.succ)
      (sampledFinal z) (Mfinal z)) F Afinal Ifinal Dfinal Mfinal Qfinal
  have hfacts := reserveProtectedPreliminaryInternalFacts hstageGood S
  have hbase : Lc.SupportedOn fun z ↦
      (∀ v, Even ((neighborsIn (Gfinal z) univ v).card)) ∧
      Gfinal z ≤ leaveGraph (Ifinal z ∪ Dfinal z) ∧
      ConsistsOfTriangles (Gfinal z) (Afinal z) ∧
      Mfinal z ⊆ Afinal z ∧
      Disjoint (Ifinal z) (Dfinal z ∪ Mfinal z) ∧
      IsPackingOn (Ifinal z ∪ (Dfinal z ∪ Mfinal z)) := by
    intro z hz
    have hzdata := hsupp z hz
    have hgood := hzdata.1
    refine ⟨heven, ?_, htri, ?_, by simp [Ifinal], ?_⟩
    · simpa only [Gfinal, Ifinal, Dfinal, empty_union] using S.hGleave
    · exact (hfacts.protectedAvailable z.1 hgood).trans
        (reserveProtectedAvailable_subset
          (reserveEdges G (W.U i.succ) (bits z.1.1)) A)
    · simpa only [Ifinal, Dfinal, empty_union, Mfinal] using
        hfacts.packing z.1 hgood
  have hinternal : Lc.SupportedOn fun z ↦
      GreedyReachable F (Ifinal z ∪ (Dfinal z ∪ Mfinal z)) (Qfinal z) ∧
      Qfinal z ⊆ Ifinal z ∪ (Dfinal z ∪ Mfinal z) ∪ Afinal z ∧
      (Qfinal z \ (Ifinal z ∪ (Dfinal z ∪ Mfinal z))).card ≤
        (internalOuterEdges (Gfinal z) (W.U i.succ)).card ∧
      ∀ e ∈ internalOuterEdges (Gfinal z) (W.U i.succ),
        (coveredGraph (Qfinal z)).Adj e.out.1 e.out.2 := by
    intro z hz
    have hzdata := hsupp z hz
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Ifinal, Dfinal, Mfinal, Qfinal, P0, empty_union] using
        hzdata.2.1
    · apply hzdata.2.2.1.trans
      intro T0 hT0
      rcases mem_union.mp hT0 with hTP0 | hTAint
      · exact mem_union_left _ (by
          simpa only [P0, Ifinal, Dfinal, Mfinal, empty_union] using hTP0)
      · exact mem_union_right _
          (pairSafeAvailable_subset_left A (P0 z.1) hTAint)
    · simpa only [Ifinal, Dfinal, Mfinal, Qfinal, P0, Gfinal,
        empty_union] using hzdata.2.2.2.1
    · simpa only [Qfinal, Gfinal] using hzdata.2.2.2.2.1
  have hlinks := hbase.rawPreliminaryInternalResidualLinks
    (U := W.U i.succ) (sampled := sampledFinal) (F := F)
    (A := Afinal) (I := Ifinal) (D := Dfinal) (Mstar := Mfinal)
    (P0 := fun z ↦ Ifinal z ∪ (Dfinal z ∪ Mfinal z)) (Q := Qfinal)
    (fun _ ↦ rfl) hinternal
  have hstruct : Lc.SupportedOn fun z ↦
      ConsistsOfTriangles (Gfinal z) (Afinal z) ∧
      Gfinal z ≤ leaveGraph (Ifinal z ∪ Dfinal z) ∧
      IsPackingOn (Ifinal z ∪ (Dfinal z ∪ Rfinal z)) ∧
      AvoidsForbidden (Ifinal z ∪ (Dfinal z ∪ Rfinal z)) F ∧
      RootedActiveCapsGood F (Qfinal z) S.R := by
    intro z hz
    have hzdata := hsupp z hz
    have hgood := hzdata.1
    have hreach : GreedyReachable F
        (Ifinal z ∪ (Dfinal z ∪ Mfinal z)) (Qfinal z) :=
      hinternal z hz |>.1
    have hpacking0 : IsPackingOn
        (Ifinal z ∪ (Dfinal z ∪ Mfinal z)) := hbase z hz |>.2.2.2.2.2
    have havoid0 : AvoidsForbidden
        (Ifinal z ∪ (Dfinal z ∪ Mfinal z)) F := by
      simpa only [Ifinal, Dfinal, Mfinal, empty_union] using
        hfacts.avoids z.1 hgood
    have hRsub : Rfinal z ⊆ Qfinal z := by
      intro T0 hT0
      rcases mem_union.mp hT0 with hTM | hTnew
      · exact hreach.initial_subset
          (by simpa only [Ifinal, Dfinal, Mfinal, empty_union] using hTM)
      · exact (mem_sdiff.mp hTnew).1
    refine ⟨htri, ?_, ?_, ?_, hzdata.2.2.2.2.2⟩
    · simpa only [Gfinal, Ifinal, Dfinal, empty_union] using S.hGleave
    · exact (hreach.isPacking hpacking0).mono (by
        simpa only [Ifinal, Dfinal, empty_union] using hRsub)
    · exact (hreach.avoidsForbidden havoid0).mono (by
        simpa only [Ifinal, Dfinal, empty_union] using hRsub)
  refine ⟨?_, ?_, ?_, hlower⟩
  · simpa only [Lc, J, LP, Kint, Kpre, P0, Aint, Gpre, bitsPre,
      initialPre, laterPre, reservePre, reserveProtectedStagePreliminaryKernel]
      using hreserve
  · simpa only [Lc, J, LP, Kint, Kpre, P0, Aint, Gpre, bitsPre,
      Ifinal, Dfinal, Mfinal, Qfinal, Rfinal, Gfinal, Afinal, sampledFinal,
      links, reserveProtectedStagePreliminaryKernel] using hlinks
  · exact hstruct

end

end Erdos207
