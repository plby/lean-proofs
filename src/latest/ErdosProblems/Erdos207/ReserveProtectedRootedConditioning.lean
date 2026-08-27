/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryInternalStage
import ErdosProblems.Erdos207.RawInternalRootedConditioning

/-!
# Rooted conditioning after the reserve-protected internal stage

The raw internal kernel may freeze, but every frozen outcome carries an exact
failure certificate.  Strong rooted concentration gives positive mass to the
event on which all those certificates are impossible.  This file specializes
that conditioning theorem to the complete protected preliminary/internal
state assembled in the preceding module.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure ReserveProtectedRootedParameters
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell)
    (level mid final : Fin (ell + 1)) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell) (cutoff : ℕ)
    (p reserveDensity C b : ℝ≥0)
    (S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b) where
  s : ℕ
  kappa : ℝ≥0
  hC : 1 ≤ 2 * S.CFinal
  hb : ∀ T : TripleSystemOn V, T.card ≤ s * (S.q - 1) →
    S.bFinal ≤ setWeight (masterUnionTriangleWeight W final S.pFinal) T
  hkappa : ∀ e : DistinctPair V,
    HasExtensionBound
      (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
        rootedThreatRemainder z)
      (masterUnionTriangleWeight W final S.pFinal) kappa
  htail : strongRootedTail V (2 * S.CFinal) kappa S.R S.q s < 1

def ReserveProtectedRootedConditioningResult
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
      TripleSystemOn V :=
    jointLater (fun _ : Omega ↦ ∅) Mstar
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
    IsReserveStronglyWellDistributed Lc W final
        (jointInitial initialPre)
        (jointLater laterPre (rawResidualInternalAdded P0))
        (fun z ↦ reservePre z.1) pFinal reserveDensityMid
        ((2 * CFinal) /
          (1 - strongRootedTail V (2 * CFinal) kappa R q s)) bFinal ∧
      Lc.SupportedOn (fun z ↦
        Good z.1 ∧
        GreedyReachable F (P0 z.1) z.2.chosen ∧
        z.2.chosen ⊆ P0 z.1 ∪ Aint z.1 ∧
        (z.2.chosen \ P0 z.1).card ≤
          (internalOuterEdges (Gpre z.1) (W.U i.succ)).card ∧
        (∀ e ∈ internalOuterEdges (Gpre z.1) (W.U i.succ),
          (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) ∧
        RootedActiveCapsGood F z.2.chosen R) ∧
      1 - strongRootedTail V (2 * CFinal) kappa R q s ≤
        J.probability RootGood

theorem ReserveProtectedPreliminaryInternalResult.conditionOn_rootedSuccess
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level mid final : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {i : Fin ell} {cutoff : ℕ}
    {p reserveDensity C b : ℝ≥0}
    {S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b}
    (hresult : ReserveProtectedPreliminaryInternalResult L W final F G A bits
      i S.n S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d
      S.D S.R S.pFinal S.reserveDensityMid S.CFinal S.bFinal)
    (T : ReserveProtectedRootedParameters L W level mid final F G A bits i
      cutoff p reserveDensity C b S) :
    ReserveProtectedRootedConditioningResult L W final F G A bits i S.n
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d S.D S.R
      S.q T.s S.pFinal S.reserveDensityMid S.CFinal S.bFinal T.kappa := by
  unfold ReserveProtectedPreliminaryInternalResult at hresult
  unfold ReserveProtectedRootedConditioningResult
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
  let initialPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := jointInitial (fun _ : Omega ↦ ∅)
  let laterPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := jointLater (fun _ : Omega ↦ ∅) Mstar
  let reservePre : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ)
      (reserveEdges G (W.U i.succ) (bits z.1)) (Mstar z.1 z.2)
  let Good : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n → Prop :=
    fun z ↦ 0 < (L.jointBind (fun omega ↦
      reserveProtectedConditionedPreliminaryKernel S.n F G (W.U i.succ)
        (reserveEdges G (W.U i.succ) (bits omega)) A ∅
        S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d)).mass z
  have hroot := hresult.1.conditionOn_rawResidualInternal_rootedSuccess
    (G := Gpre) (A := Aint) (P0 := P0) (bits := bitsPre)
    (initial := initialPre) (later := laterPre) (reserve := reservePre)
    i Good hresult.2 (by
      intro z _hz
      simp only [initialPre, laterPre, P0, jointInitial, jointLater,
        empty_union]) T.hC S.hfamily T.hb T.kappa T.hkappa T.htail
  unfold reserveProtectedStagePreliminaryKernel
  simpa only [Kpre, Mstar, LP, P0, Aint, Gpre, bitsPre, initialPre,
    laterPre, reservePre, Good, reserveProtectedStagePreliminaryAdded,
    reserveProtectedStagePreliminaryGood] using hroot

end

end Erdos207
