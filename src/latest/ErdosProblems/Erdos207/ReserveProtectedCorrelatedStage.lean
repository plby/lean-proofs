/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryInternalStage
import ErdosProblems.Erdos207.ReserveProtectedCorrelatedComposition

/-!
# Complete reserve-protected correlated preliminary/internal stage

This is the quantitative replacement for the sequential stage constructor.
The preliminary and scheduled-internal choices enter one master update with
the combined base `alpha + eta * D⁻¹`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ReserveProtectedCorrelatedResult
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (final : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell) (n : ℕ)
    (Kpair Kglobal Kinc Delta delta Icut Dcut d D R : ℕ)
    (pFinal reserveDensityFinal CFinal bFinal : ℝ≥0) : Prop :=
  let Kpre := reserveProtectedStagePreliminaryKernel W F G A bits i n
    Kpair Kglobal Kinc Delta delta Icut Dcut d
  let Mstar : Omega → FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := reserveProtectedStagePreliminaryAdded
  let P0 : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ Mstar z.1 z.2
  let Aint : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ pairSafeAvailable A (P0 z)
  let Gpre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      SimpleGraph V := fun _ ↦ G
  let bitsPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      Sym2 V → Bool := fun z ↦ bits z.1
  let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre D
  let K : Omega → FiniteLaw
      (FiniteLaw.TimedState (GreedyStateOn V) n ×
        InternalEdgeGreedyStateOn V) := fun omega ↦
    (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi))
  let added : Omega →
      FiniteLaw.TimedState (GreedyStateOn V) n ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun omega z ↦
    preliminaryInternalCombinedAdded (Mstar omega)
      (fun xi w ↦ rawResidualInternalAdded P0 (omega, xi) w) z
  IsReserveStronglyWellDistributed (L.jointBind K) W final
      (jointInitial (fun _ ↦ (∅ : TripleSystemOn V)))
      (jointLater (fun _ ↦ (∅ : TripleSystemOn V)) added)
      (fun z ↦ preliminaryAugmentedReserve G (W.U i.succ)
        (reserveEdges G (W.U i.succ) (bits z.1)) (added z.1 z.2))
      pFinal reserveDensityFinal (2 * CFinal) bFinal ∧
    (L.jointBind K).SupportedOn (fun z ↦
      reserveProtectedStagePreliminaryGood L Kpre (z.1, z.2.1) ∧
        RawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre D R
          (z.1, z.2.1) z.2.2)

theorem IsReserveStronglyWellDistributed.bind_reserveProtectedCorrelatedStage
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level mid final : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A : TripleSystemOn V} {bits : Omega → Sym2 V → Bool}
    {p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (htri : ConsistsOfTriangles G A)
    (hstrong : IsReserveStronglyWellDistributed L W level
      (fun _ ↦ (∅ : TripleSystemOn V)) (fun _ ↦ ∅)
      (fun omega ↦ reserveEdges G (W.U i.succ) (bits omega))
      p reserveDensity C b)
    (cutoff : ℕ)
    (hstageGood : L.SupportedOn fun omega ↦
      ReserveProtectedStageGood W i G A ∅ cutoff (bits omega))
    (S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b) :
    ReserveProtectedCorrelatedResult L W final F G A bits i S.n
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d S.D S.R
      S.pFinal S.reserveDensityMid S.CFinal S.bFinal := by
  have hfacts := reserveProtectedPreliminaryInternalFacts hstageGood S
  unfold ReserveProtectedCorrelatedResult
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
  let added : Omega →
      FiniteLaw.TimedState (GreedyStateOn V) S.n ×
        InternalEdgeGreedyStateOn V → TripleSystemOn V := fun omega z ↦
    preliminaryInternalCombinedAdded (Mstar omega)
      (fun xi w ↦ rawResidualInternalAdded P0 (omega, xi) w) z
  let Good : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n → Prop :=
    reserveProtectedStagePreliminaryGood L Kpre
  have htriInt : ∀ z, Good z → ConsistsOfTriangles (Gpre z) (Aint z) :=
    fun z _ ↦ htri.pairSafeAvailable
  have hinitial : ∀ z, Good z → ∀ T ∈ Aint z,
      TriangleAvoidsGraph (coveredGraph (P0 z)) T := by
    intro z _ T hT
    exact pairSafeAvailable_triangleAvoids A (P0 z) T hT
  have hsupply : ∀ z, Good z →
      let E := preliminaryResidualInternalEdges
        (Gpre z) (W.U i.succ) (P0 z)
      ∀ e ∈ E,
        S.a + S.D ≤ (activeReserveWedgeVertices (Gpre z) (W.U i.succ)
          (residualInternalExtensionSet W i (Aint z) e)
          e.out.1 e.out.2 (bitsPre z)).card := by
    intro z hz
    dsimp only [Gpre, P0]
    intro e he
    have heInternal : e ∈ internalOuterEdges G (W.U i.succ) :=
      preliminaryResidualInternalEdges_subset_internalOuterEdges
        G (W.U i.succ) (P0 z) he
    have hbase := hfacts.supply z hz e heInternal
    have he' : e ∈ preliminaryResidualInternalEdges G (W.U i.succ)
        ((∅ : TripleSystemOn V) ∪ Mstar z.1 z.2) := by
      simpa only [P0, empty_union] using he
    have hM : Mstar z.1 z.2 ⊆ reserveProtectedAvailable
        (reserveEdges G (W.U i.succ) (bits z.1)) A := by
      exact hfacts.protectedAvailable z hz
    have hmono := card_activeReserveWedgeVertices_pairSafe_ge
      (A := A) (P := (∅ : TripleSystemOn V)) (M := Mstar z.1 z.2)
      (bits := bits z.1) he' S.hGleave hM
    exact hbase.trans (by
      simpa only [Gpre, Aint, P0, bitsPre, residualInternalExtensionSet,
        empty_union] using hmono)
  have hkernel := rawResidualInternalKernel_of_fixedReserveSupply
    Good htriInt i
      (fun z hz ↦ by simpa only [P0] using hfacts.packing z hz)
      (fun z hz ↦ by simpa only [P0] using hfacts.avoids z hz)
      hinitial bitsPre S.a S.D S.d S.R S.q S.hD hsupply S.hfamily
      (fun z hz v ↦ by
        simpa only [Gpre, P0] using hfacts.incidence z hz v)
      S.hscalar
  have hCCFinal : C ≤ S.CFinal := by
    calc
      C ≤ S.CMid := S.hCCMid
      _ ≤ 2 * S.CMid := by
        simpa only [two_mul] using
          (le_add_self : S.CMid ≤ S.CMid + S.CMid)
      _ ≤ S.CFinal := S.hCFinal
  have hpFinal' : p ≤ S.pFinal := S.hpMid.trans S.hpFinal
  have hbFinal' : b ≤ S.bFinal := S.hbMid.trans S.hbFinal
  have hresult :=
    hstrong.jointBind_protectedPreliminary_rawInternal_correlated
      (U := W.U i.succ) (Aint := Aint) (i := i) rfl Mstar Good
      (fun omega ↦
        reserveEdges_subset_crossingEdges G (W.U i.succ) (bits omega))
      (by
        intro omega hmass Q E
        simpa only [Kpre, Mstar] using hfacts.preliminaryOuter omega hmass Q E)
      (by simpa only [Good, Kpre] using hfacts.support)
      (fun z hz ↦ by simpa only [Mstar] using hfacts.packing z hz)
      (by simpa only [Gpre, Aint, P0, bitsPre] using hkernel.1)
      (by simpa only [Gpre, Aint, P0, bitsPre, Kint] using hkernel.2)
      S.hnonempty (S.hlevelMid.trans S.hmidFinal) hCCFinal S.hCFinalOne
      hpFinal' S.hpOne S.hreserveMono S.hreserveOne S.hcombinedOne
      S.hetaOne S.hetaReserve S.hbOne hbFinal' S.hnewCombined
  simpa only [Kpre, Mstar, P0, Aint, Gpre, bitsPre, Kint, K, added,
    reserveProtectedStagePreliminaryKernel,
    reserveProtectedStagePreliminaryAdded] using hresult

end

end Erdos207
