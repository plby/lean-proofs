/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryKernel
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryInternalComposition
import ErdosProblems.Erdos207.ReserveProtectedStageGood

/-!
# The reserve-protected preliminary/internal stage

This file inserts the total twice-conditioned preliminary kernel into an
already conditioned reserve law.  It is the support-level bridge between the
common reserve-good event and the raw retrospective internal cover.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The complete law-and-support conclusion of the protected preliminary
stage followed by the raw internal cover.  Naming this large dependent
expression keeps downstream theorem reduction within Lean's default budget. -/
def ReserveProtectedPreliminaryInternalResult
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (final : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell) (n : ℕ)
    (Kpair Kglobal Kinc Delta delta Icut Dcut d D R : ℕ)
    (pFinal reserveDensityMid CFinal bFinal : ℝ≥0) : Prop :=
  let Kpre : Omega →
      FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) := fun omega ↦
    reserveProtectedConditionedPreliminaryKernel n F G (W.U i.succ)
      (reserveEdges G (W.U i.succ) (bits omega)) A ∅
      Kpair Kglobal Kinc Delta delta Icut Dcut d
  let Mstar : Omega → FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun _ z ↦ z.2.chosen
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
  let reservePre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ)
      (reserveEdges G (W.U i.succ) (bits z.1)) (Mstar z.1 z.2)
  IsReserveStronglyWellDistributed (LP.jointBind Kint) W final
      (jointInitial (jointInitial (fun _ : Omega ↦
        (∅ : TripleSystemOn V))))
      (jointLater
        (jointLater (fun _ : Omega ↦ (∅ : TripleSystemOn V)) Mstar)
        (rawResidualInternalAdded P0))
      (fun z ↦ reservePre z.1) pFinal reserveDensityMid
      (2 * CFinal) bFinal ∧
    (LP.jointBind Kint).SupportedOn (fun z ↦
      0 < LP.mass z.1 ∧
        RawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre
          D R z.1 z.2)

/-- Numerical and finite-process hypotheses for one protected preliminary
and raw internal stage.  Bundling them avoids repeatedly normalizing the
same large dependent parameter telescope. -/
structure ReserveProtectedPreliminaryInternalParameters
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell)
    (level mid final : Fin (ell + 1)) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell)
    (cutoff : ℕ) (p reserveDensity C b : ℝ≥0) where
  n : ℕ
  Kpair : ℕ
  Kglobal : ℕ
  Kinc : ℕ
  Delta : ℕ
  delta : ℕ
  Icut : ℕ
  Dcut : ℕ
  M : ℕ
  supply : ℕ
  d : ℕ
  hDcut : 0 < Dcut
  hsupplyM : (supply : ℕ) ≤ M
  h3supply : 3 * (supply : ℕ) ≤ delta
  alpha : ℝ≥0
  eta : ℝ≥0
  epsilon : ℝ≥0
  hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A)
  hGleave : G ≤ leaveGraph (∅ : TripleSystemOn V)
  hsmall : 3 + Kpair < delta
  hactive₀ : ∀ omega, 0 < L.mass omega →
    timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut 0
        (relativePreliminaryInitialState ∅
          (reserveProtectedOuterAvailable G (W.U i.succ)
            (reserveEdges G (W.U i.succ) (bits omega)) A))
  hupper : ∀ omega, 0 < L.mass omega → ∀ j S,
    timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut j S →
    S.available.card ≤ M
  hselected : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ alpha
  hsurvived : ∀ Q : TripleSystemOn V,
    ((((M - supply : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
      (n - Q.card)) ≤ eta
  hinactive : ∀ omega, 0 < L.mass omega →
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta Icut Dcut)
      (relativePreliminaryInitialState ∅
        (reserveProtectedOuterAvailable G (W.U i.succ)
          (reserveEdges G (W.U i.succ) (bits omega)) A))).probability
      (fun z ↦ ¬ timedAggregateAveragePairBandActive F Kpair Kglobal
        Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon
  hepsilon : epsilon < 1
  htail : residualOuterIncidenceTail V
    (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
    (eta / (1 - epsilon)) (d + 1) < 1
  pMid : ℝ≥0
  reserveDensityMid : ℝ≥0
  CMid : ℝ≥0
  bMid : ℝ≥0
  pFinal : ℝ≥0
  CFinal : ℝ≥0
  bFinal : ℝ≥0
  hnonempty : ∀ j, (W.U j).Nonempty
  hlevelMid : level ≤ mid
  hCCMid : C ≤ CMid
  hCMid : 1 ≤ CMid
  hpMid : p ≤ pMid
  hpOne : p ≤ 1
  hreserveMono : reserveDensity ≤ reserveDensityMid
  hreserveOne : reserveDensity ≤ 1
  halpha : alpha / (1 - epsilon) /
      (1 - residualOuterIncidenceTail V
        (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
        (eta / (1 - epsilon)) (d + 1)) ≤ 1
  hetaOne : eta / (1 - epsilon) /
      (1 - residualOuterIncidenceTail V
        (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
        (eta / (1 - epsilon)) (d + 1)) ≤ 1
  hetaReserve : eta / (1 - epsilon) /
      (1 - residualOuterIncidenceTail V
        (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
        (eta / (1 - epsilon)) (d + 1)) ≤ reserveDensityMid
  hbOne : b ≤ 1
  hbMid : b ≤ bMid
  hnewPre : ∀ Q : TripleOn V,
    alpha / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V
          (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
          (eta / (1 - epsilon)) (d + 1)) ≤
      pMid / ((W.U (W.truncatedLevel mid Q)).card : ℝ≥0)
  a : ℕ
  D : ℕ
  R : ℕ
  q : ℕ
  hD : 0 < D
  hcutoff : a + D ≤ cutoff
  hfamily : ∀ S ∈ F, S.card ≤ q
  hscalar : 4 * d + R * q ≤ a
  hmidFinal : mid ≤ final
  hCFinal : 2 * CMid ≤ CFinal
  hCFinalOne : 1 ≤ CFinal
  hpFinal : pMid ≤ pFinal
  hfactor : (D : ℝ≥0)⁻¹ ≤ 1
  hbFinal : bMid ≤ bFinal
  hcombinedOne :
    alpha / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V
          (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
          (eta / (1 - epsilon)) (d + 1)) +
      (eta / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V
          (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
          (eta / (1 - epsilon)) (d + 1))) * (D : ℝ≥0)⁻¹ ≤ 1
  hnewCombined : ∀ T : TripleOn V,
    alpha / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V
          (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
          (eta / (1 - epsilon)) (d + 1)) +
      (eta / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V
          (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
          (eta / (1 - epsilon)) (d + 1))) * (D : ℝ≥0)⁻¹ ≤
      pFinal / ((W.U (W.truncatedLevel final T)).card : ℝ≥0)

def reserveProtectedStagePreliminaryKernel
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (A : TripleSystemOn V) (bits : Omega → Sym2 V → Bool)
    (i : Fin ell) (n Kpair Kglobal Kinc Delta delta Icut Dcut d : ℕ)
    (omega : Omega) :
    FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) :=
  reserveProtectedConditionedPreliminaryKernel n F G (W.U i.succ)
    (reserveEdges G (W.U i.succ) (bits omega)) A ∅
    Kpair Kglobal Kinc Delta delta Icut Dcut d

def reserveProtectedStagePreliminaryAdded
    {Omega V : Type*} [DecidableEq V] {n : ℕ}
    (_omega : Omega) (z : FiniteLaw.TimedState (GreedyStateOn V) n) :
    TripleSystemOn V := z.2.chosen

def reserveProtectedStagePreliminaryGood
    {Omega Xi : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (z : Omega × Xi) : Prop :=
  0 < (L.jointBind K).mass z

structure ReserveProtectedPreliminaryInternalFacts
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell)
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (A : TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (i : Fin ell) (cutoff : ℕ)
    {level mid final : Fin (ell + 1)} {p reserveDensity C b : ℝ≥0}
    (S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b) where
  preliminary : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d omega).probability
        (fun xi ↦
        Q ⊆ reserveProtectedStagePreliminaryAdded omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges G (W.U i.succ)
          (reserveProtectedStagePreliminaryAdded omega xi) \
            reserveEdges G (W.U i.succ) (bits omega)) ≤
      (S.alpha / (1 - S.epsilon) /
          (1 - residualOuterIncidenceTail V
            (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
            (S.eta / (1 - S.epsilon)) (S.d + 1))) ^ Q.card *
      (S.eta / (1 - S.epsilon) /
          (1 - residualOuterIncidenceTail V
            (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
            (S.eta / (1 - S.epsilon)) (S.d + 1))) ^ E.card + 0
  preliminaryOuter : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d omega).probability
        (fun xi ↦
        Q ⊆ reserveProtectedStagePreliminaryAdded omega xi ∧
        E ⊆ preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G (W.U i.succ)
            (reserveEdges G (W.U i.succ) (bits omega)))
          (W.U i.succ)
          (reserveProtectedStagePreliminaryAdded omega xi)) ≤
      (S.alpha / (1 - S.epsilon) /
          (1 - residualOuterIncidenceTail V
            (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
            (S.eta / (1 - S.epsilon)) (S.d + 1))) ^ Q.card *
        (S.eta / (1 - S.epsilon) /
          (1 - residualOuterIncidenceTail V
            (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
            (S.eta / (1 - S.epsilon)) (S.d + 1))) ^ E.card
  support : FiniteLaw.SupportedOn
    (reserveProtectedStagePreliminaryGood L
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d))
    (L.jointBind (reserveProtectedStagePreliminaryKernel W F G A bits
      i S.n S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d))
  protectedAvailable : ∀ z, reserveProtectedStagePreliminaryGood L
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d) z →
    reserveProtectedStagePreliminaryAdded z.1 z.2 ⊆
      reserveProtectedAvailable
        (reserveEdges G (W.U i.succ) (bits z.1)) A
  packing : ∀ z, reserveProtectedStagePreliminaryGood L
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d) z →
    IsPackingOn (reserveProtectedStagePreliminaryAdded z.1 z.2)
  avoids : ∀ z, reserveProtectedStagePreliminaryGood L
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d) z →
    AvoidsForbidden (reserveProtectedStagePreliminaryAdded z.1 z.2) F
  supply : ∀ z, reserveProtectedStagePreliminaryGood L
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d) z →
    ∀ e ∈ internalOuterEdges G (W.U i.succ),
      S.a + S.D ≤ (activeReserveWedgeVertices G (W.U i.succ)
        (iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ))
        e.out.1 e.out.2 (bits z.1)).card
  incidence : ∀ z, reserveProtectedStagePreliminaryGood L
      (reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
        S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d) z →
    ∀ v : V, (scheduledEdgesAt
      (preliminaryResidualInternalEdges G (W.U i.succ)
        (reserveProtectedStagePreliminaryAdded z.1 z.2)) v).card ≤ S.d

theorem reserveProtectedPreliminaryInternalFacts
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level mid final : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {i : Fin ell} {cutoff : ℕ}
    {p reserveDensity C b : ℝ≥0}
    (hstageGood : L.SupportedOn fun omega ↦
      ReserveProtectedStageGood W i G A ∅ cutoff (bits omega))
    (S : ReserveProtectedPreliminaryInternalParameters L W level mid final
      F G A bits i cutoff p reserveDensity C b) :
    ReserveProtectedPreliminaryInternalFacts L W F G A bits i cutoff S := by
  let Kpre : Omega →
      FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) S.n) :=
    reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
      S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d
  let Mstar : Omega → FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := reserveProtectedStagePreliminaryAdded
  let Good : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n → Prop :=
    fun z ↦ 0 < (L.jointBind Kpre).mass z
  have hSpec (omega : Omega) (hmass : 0 < L.mass omega) :=
    reserveProtectedConditionedPreliminaryKernel_spec S.n F G (W.U i.succ)
      (reserveEdges G (W.U i.succ) (bits omega)) A ∅
      (reserveEdges_subset_crossingEdges G (W.U i.succ) (bits omega))
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.M S.supply
      S.d S.hDcut S.hsupplyM S.h3supply S.alpha S.eta S.epsilon S.hInv
      S.hGleave (hstageGood omega hmass).2 S.hsmall (S.hactive₀ omega hmass)
      (S.hupper omega hmass) S.hselected S.hsurvived (S.hinactive omega hmass)
      S.hepsilon S.htail
  have hSpecOuter (omega : Omega) (hmass : 0 < L.mass omega) :=
    reserveProtectedConditionedPreliminaryKernel_outerProduct S.n F G
      (W.U i.succ) (reserveEdges G (W.U i.succ) (bits omega)) A ∅
      (reserveEdges_subset_crossingEdges G (W.U i.succ) (bits omega))
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.M S.supply
      S.d S.hDcut S.hsupplyM S.h3supply S.alpha S.eta S.epsilon S.hInv
      S.hGleave (hstageGood omega hmass).2 S.hsmall (S.hactive₀ omega hmass)
      (S.hupper omega hmass) S.hselected S.hsurvived (S.hinactive omega hmass)
      S.hepsilon S.htail
  have hmassL : ∀ z, Good z → 0 < L.mass z.1 := by
    intro z hz
    exact (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2).mp hz |>.1
  have hmassK : ∀ z, Good z → 0 < (Kpre z.1).mass z.2 := by
    intro z hz
    exact (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2).mp hz |>.2
  refine ⟨?_, ?_, (fun _ hz ↦ hz), ?_, ?_, ?_, ?_, ?_⟩
  · intro omega hmass Q E
    simpa only [Kpre, Mstar, reserveProtectedStagePreliminaryKernel,
      reserveProtectedStagePreliminaryAdded, sdiff_empty, add_zero] using
      (hSpec omega hmass).2.2.1 Q E
  · intro omega hmass Q E
    simpa only [Kpre, Mstar, reserveProtectedStagePreliminaryKernel,
      reserveProtectedStagePreliminaryAdded, sdiff_empty] using
      hSpecOuter omega hmass Q E
  · intro z hz
    simpa only [Mstar, reserveProtectedStagePreliminaryAdded, sdiff_empty] using
      (hSpec z.1 (hmassL z hz)).2.2.2.1 z.2 (hmassK z hz)
  · intro z hz
    have htraj := (hSpec z.1 (hmassL z hz)).2.1 z.2 (hmassK z hz)
    have hs := htraj.structural_newPart
      (I := (∅ : TripleSystemOn V)) (D := ∅)
      (A := reserveProtectedOuterAvailable G (W.U i.succ)
        (reserveEdges G (W.U i.succ) (bits z.1)) A) rfl rfl (by simp)
    simpa only [Mstar, reserveProtectedStagePreliminaryAdded,
      relativePreliminaryInitialState_chosen, sdiff_empty, empty_union] using hs.2.2
  · intro z hz
    have htraj := (hSpec z.1 (hmassL z hz)).2.1 z.2 (hmassK z hz)
    have hinv := htraj.1.2.1
    simpa only [Mstar, reserveProtectedStagePreliminaryAdded,
      relativePreliminaryInitialState_chosen, sdiff_empty, empty_union] using hinv
  · intro z hz e he
    exact S.hcutoff.trans
      (Nat.le_of_lt ((hstageGood z.1 (hmassL z hz)).1 e he))
  · intro z hz v
    simpa [Mstar, reserveProtectedStagePreliminaryAdded] using
      (hSpec z.1 (hmassL z hz)).2.2.2.2 z.2 (hmassK z hz) v

theorem IsReserveStronglyWellDistributed.bind_reserveProtectedPreliminary_fixedInternal
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
      F G A bits i cutoff p reserveDensity C b)
    (hnewInternal : ∀ T : TripleOn V,
      (S.D : ℝ≥0)⁻¹ ≤
        S.pFinal /
          ((W.U (W.truncatedLevel final T)).card : ℝ≥0)) :
    ReserveProtectedPreliminaryInternalResult L W final F G A bits i S.n
      S.Kpair S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d S.D S.R
      S.pFinal S.reserveDensityMid S.CFinal S.bFinal := by
  have hfacts := reserveProtectedPreliminaryInternalFacts hstageGood S
  unfold ReserveProtectedPreliminaryInternalResult
  let Kpre : Omega →
      FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) S.n) :=
    reserveProtectedStagePreliminaryKernel W F G A bits i S.n S.Kpair
      S.Kglobal S.Kinc S.Delta S.delta S.Icut S.Dcut S.d
  let Mstar : Omega → FiniteLaw.TimedState (GreedyStateOn V) S.n →
      TripleSystemOn V := reserveProtectedStagePreliminaryAdded
  let Good : Omega × FiniteLaw.TimedState (GreedyStateOn V) S.n → Prop :=
    reserveProtectedStagePreliminaryGood L Kpre
  have hresult :=
    hstrong.jointBind_reserveProtectedPreliminary_fixedInternal
      (G := fun _ : Omega ↦ G) (A := fun _ : Omega ↦ A)
      (P := fun _ : Omega ↦ (∅ : TripleSystemOn V)) (bits := bits)
      i Mstar
      hfacts.preliminary S.hnonempty S.hlevelMid S.hCCMid S.hCMid
      S.hpMid S.hpOne
      S.hreserveMono S.hreserveOne S.halpha S.hetaOne S.hetaReserve S.hbOne
      (by simpa using S.hbMid) S.hnewPre Good hfacts.support
      (fun _ _ ↦ htri)
      (fun _ _ ↦ S.hGleave) hfacts.protectedAvailable
      (fun z hz ↦ by simpa only [empty_union] using hfacts.packing z hz)
      (fun z hz ↦ by simpa only [empty_union] using hfacts.avoids z hz)
      S.a S.D S.d S.R S.q S.hD hfacts.supply S.hfamily
      (fun z hz v ↦ by
        simpa only [empty_union] using hfacts.incidence z hz v)
      S.hscalar
      S.hmidFinal S.hCFinal S.hCFinalOne S.hpFinal S.hfactor S.hbFinal
      hnewInternal
  exact hresult

end

end Erdos207
