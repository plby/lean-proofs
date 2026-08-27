/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedCorrelatedStage
import ErdosProblems.Erdos207.CorrelatedRootedResidualLinks
import ErdosProblems.Erdos207.ReserveProtectedRootedConditioning

/-!
# Rooted residual-link output of the correlated protected stage
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ReserveProtectedCorrelatedConditionedResult
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell)
    (level mid final : Fin (ell + 1)) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell) (cutoff : ℕ)
    (p reserveDensity C b : ℝ≥0)
    (S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b)
    (T : ReserveProtectedRootedParameters L W level mid final F G A bits i
      cutoff p reserveDensity C b S) : Prop :=
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
  let total : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → TripleSystemOn V := fun z ↦
    preliminaryInternalCombinedAdded
      (fun _ : FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
        P0 (z.1, z.2.1))
      (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
  let sampled : Omega → Finset (Sym2 V) := fun omega ↦
    reserveEdges G (W.U i.succ) (bits omega)
  let reserve : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ) (sampled z.1) (total z)
  let RootGood : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Prop := fun z ↦
    RootedActiveCapsGood F (total z) S.R
  ∃ hpos : 0 < J.probability RootGood,
    let Lc := J.conditionOn RootGood hpos
    IsReserveStronglyWellDistributed Lc W final
        (fun _ ↦ (∅ : TripleSystemOn V)) total reserve S.pFinal
        S.reserveDensityMid
        ((2 * S.CFinal) /
          (1 - strongRootedTail V (2 * S.CFinal) T.kappa S.R S.q T.s))
        S.bFinal ∧
      Lc.SupportedOn (fun z ↦
        reserveProtectedStagePreliminaryGood L Kpre (z.1, z.2.1) ∧
          RawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre
            S.D S.R (z.1, z.2.1) z.2.2 ∧
          RootedActiveCapsGood F z.2.2.chosen S.R) ∧
      1 - strongRootedTail V (2 * S.CFinal) T.kappa S.R S.q T.s ≤
        J.probability RootGood

def ReserveProtectedCorrelatedRootedResult
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell)
    (level mid final : Fin (ell + 1)) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell) (cutoff : ℕ)
    (p reserveDensity C b : ℝ≥0)
    (S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b)
    (T : ReserveProtectedRootedParameters L W level mid final F G A bits i
      cutoff p reserveDensity C b S) : Prop :=
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
  let total : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → TripleSystemOn V := fun z ↦
    preliminaryInternalCombinedAdded
      (fun _ : FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
        P0 (z.1, z.2.1))
      (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
  let sampled : Omega → Finset (Sym2 V) := fun omega ↦
    reserveEdges G (W.U i.succ) (bits omega)
  let reserve : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ) (sampled z.1) (total z)
  let RootGood : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Prop := fun z ↦
    RootedActiveCapsGood F (total z) S.R
  ∃ hpos : 0 < J.probability RootGood,
    let Lc := J.conditionOn RootGood hpos
    let links := Erdos207.internalOutcomeResidualLinks (fun _ ↦ G)
      (W.U i.succ) reserve F (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
      total (fun z ↦ z.2.2.chosen)
    IsReserveStronglyWellDistributed Lc W final
        (fun _ ↦ (∅ : TripleSystemOn V)) total reserve S.pFinal
        S.reserveDensityMid
        ((2 * S.CFinal) /
          (1 - strongRootedTail V (2 * S.CFinal) T.kappa S.R S.q T.s))
        S.bFinal ∧
      Lc.SupportedOn (fun z ↦
        IsIntermediateLinkState G (W.U i.succ) A ∅ ∅
            (internalStageFamily ∅ ∅ (total z) z.2.2.chosen)
            (links z) ∧
          (∀ o, (links z o).center =
            outsideVertexEmbedding (W.U i.succ) o) ∧
          (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
          (∀ o, (links z o).left ⊆ W.U i.succ) ∧
          (∀ o, (links z o).right ⊆ W.U i.succ) ∧
          (∀ o, (links z o).SpokesIn (reserve z))) ∧
      Lc.SupportedOn (fun z ↦
        ConsistsOfTriangles G A ∧ G ≤ leaveGraph (∅ : TripleSystemOn V) ∧
          IsPackingOn (internalStageFamily ∅ ∅ (total z) z.2.2.chosen) ∧
          AvoidsForbidden
            (internalStageFamily ∅ ∅ (total z) z.2.2.chosen) F ∧
          RootedActiveCapsGood F z.2.2.chosen S.R) ∧
      1 - strongRootedTail V (2 * S.CFinal) T.kappa S.R S.q T.s ≤
        J.probability RootGood

theorem ReserveProtectedCorrelatedResult.conditionOn_rooted
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
    (hresult : ReserveProtectedCorrelatedResult L W final F G A bits i S.n
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d S.D S.R
      S.pFinal S.reserveDensityMid S.CFinal S.bFinal) :
    ReserveProtectedCorrelatedConditionedResult L W level mid final F G A
      bits i cutoff p reserveDensity C b S T := by
  unfold ReserveProtectedCorrelatedResult at hresult
  unfold ReserveProtectedCorrelatedConditionedResult
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
  let total : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → TripleSystemOn V := fun z ↦
    preliminaryInternalCombinedAdded
      (fun _ : FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
        P0 (z.1, z.2.1))
      (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
  let sampled : Omega → Finset (Sym2 V) := fun omega ↦
    reserveEdges G (W.U i.succ) (bits omega)
  let reserve : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ) (sampled z.1) (total z)
  let RootGood : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Prop := fun z ↦
    RootedActiveCapsGood F (total z) S.R
  have hdist : IsReserveStronglyWellDistributed J W final
      (fun _ ↦ (∅ : TripleSystemOn V)) total reserve S.pFinal
      S.reserveDensityMid (2 * S.CFinal) S.bFinal := by
    convert hresult.1 using 1
    · rfl
    · funext z
      simp only [total, jointLater, empty_union, P0, Mstar,
        preliminaryInternalCombinedAdded]
    · funext z
      simp only [reserve, sampled, total, P0, Mstar,
        preliminaryInternalCombinedAdded]
  have hroot := hdist.conditionOn_rootedActiveCapsGood T.hC S.hfamily T.hb
    T.kappa T.hkappa T.htail
  obtain ⟨hpos, hdistC, hrootSupport, hlower⟩ := hroot
  refine ⟨hpos, hdistC, ?_, hlower⟩
  let Lc := J.conditionOn RootGood hpos
  have hrawC : Lc.SupportedOn fun z ↦
      reserveProtectedStagePreliminaryGood L Kpre (z.1, z.2.1) ∧
        RawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre S.D S.R
          (z.1, z.2.1) z.2.2 := by
    simpa only [Lc, J, K, Kpre, Gpre, Aint, P0, bitsPre, Kint] using
      hresult.2.conditionOn hpos
  intro z hz
  have hr := hrawC z hz
  have hrootTotal := hrootSupport z (by simpa only [Lc, RootGood] using hz)
  have htotal : total z = z.2.2.chosen := by
    dsimp only [total, preliminaryInternalCombinedAdded]
    exact union_sdiff_of_subset hr.2.1.1.initial_subset
  exact ⟨hr.1, hr.2, by simpa only [RootGood, htotal] using hrootTotal⟩

theorem ReserveProtectedCorrelatedResult.rootedResidualLinks
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
    (hresult : ReserveProtectedCorrelatedResult L W final F G A bits i S.n
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d S.D S.R
      S.pFinal S.reserveDensityMid S.CFinal S.bFinal)
    (hstageGood : L.SupportedOn fun omega ↦
      ReserveProtectedStageGood W i G A ∅ cutoff (bits omega))
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (htri : ConsistsOfTriangles G A) :
    ReserveProtectedCorrelatedRootedResult L W level mid final F G A bits i
      cutoff p reserveDensity C b S T := by
  have hconditioned := hresult.conditionOn_rooted (T := T)
  unfold ReserveProtectedCorrelatedConditionedResult at hconditioned
  unfold ReserveProtectedCorrelatedRootedResult
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
  let total : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → TripleSystemOn V := fun z ↦
    preliminaryInternalCombinedAdded
      (fun _ : FiniteLaw.TimedState (GreedyStateOn V) S.n ↦
        P0 (z.1, z.2.1))
      (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
  let sampled : Omega → Finset (Sym2 V) := fun omega ↦
    reserveEdges G (W.U i.succ) (bits omega)
  let reserve : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ) (sampled z.1) (total z)
  let RootGood : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) → Prop := fun z ↦
    RootedActiveCapsGood F (total z) S.R
  obtain ⟨hpos, hdistC, hsupp, hlower⟩ := hconditioned
  refine ⟨hpos, ?_⟩
  let Lc := J.conditionOn RootGood hpos
  have hfacts := reserveProtectedPreliminaryInternalFacts hstageGood S
  have hP0 : ∀ z, reserveProtectedStagePreliminaryGood L Kpre z →
      P0 z ⊆ A := by
    intro z hz
    exact (hfacts.protectedAvailable z (by simpa only [Kpre] using hz)).trans
      (reserveProtectedAvailable_subset
        (reserveEdges G (W.U i.succ) (bits z.1)) A)
  have hAint : ∀ z, reserveProtectedStagePreliminaryGood L Kpre z →
      Aint z ⊆ A := by
    intro z _
    exact pairSafeAvailable_subset_left A (P0 z)
  have hpacking : ∀ z, reserveProtectedStagePreliminaryGood L Kpre z →
      IsPackingOn (P0 z) := by
    intro z hz
    simpa only [P0, Mstar, Kpre] using hfacts.packing z hz
  have hlinks := hsupp.correlatedRawInternalResidualLinks
    (sampled := sampled) hP0 hAint hpacking (fun _ ↦ heven)
    (fun _ ↦ S.hGleave) (fun _ ↦ htri)
  let links := Erdos207.internalOutcomeResidualLinks (fun _ : Omega ×
      (FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V) ↦ G)
      (W.U i.succ) reserve F (fun _ ↦ A) (fun _ ↦ ∅) (fun _ ↦ ∅)
      total (fun z ↦ z.2.2.chosen)
  have hstruct : Lc.SupportedOn fun z ↦
      ConsistsOfTriangles G A ∧ G ≤ leaveGraph (∅ : TripleSystemOn V) ∧
        IsPackingOn (internalStageFamily ∅ ∅ (total z) z.2.2.chosen) ∧
        AvoidsForbidden
          (internalStageFamily ∅ ∅ (total z) z.2.2.chosen) F ∧
        RootedActiveCapsGood F z.2.2.chosen S.R := by
    intro z hz
    have hd := hsupp z hz
    have htotal : total z = z.2.2.chosen := by
      dsimp only [total, preliminaryInternalCombinedAdded]
      exact union_sdiff_of_subset hd.2.1.1.1.initial_subset
    have hreach := hd.2.1.1.1
    have hpackChosen := hreach.isPacking (hpacking (z.1, z.2.1) hd.1)
    have havoidChosen := hreach.avoidsForbidden
      (hfacts.avoids (z.1, z.2.1) (by simpa only [Kpre] using hd.1))
    have hstageEq : internalStageFamily ∅ ∅ (total z) z.2.2.chosen =
        z.2.2.chosen := by
      rw [htotal]
      ext T0
      simp [internalStageFamily]
    refine ⟨htri, S.hGleave, ?_, ?_, hd.2.2⟩
    · simpa only [hstageEq] using hpackChosen
    · simpa only [hstageEq] using havoidChosen
  refine ⟨?_, ?_, hstruct, ?_⟩
  · simpa only [Lc, J, RootGood] using hdistC
  · simpa only [Lc, J, Kpre, Mstar, P0, Aint, Gpre, bitsPre, Kint, K,
      total, sampled, reserve, links] using hlinks
  · simpa only [J, K, RootGood] using hlower

end

end Erdos207
