/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConditionedCompressedFullReserveStage
import ErdosProblems.Erdos207.ReserveSampledLinkConcentration

/-!
# Density-one reserve stage with deterministic link bounds

The full crossing reserve has no reserve-conditioning loss.  In addition to
the protected-stage event, iteration typicality deterministically gives all
degree and codegree bounds that are relevant to residual graph links.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsCompressedMasterLaw.exists_conditionedFullTypicalReserveStage
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C b Cpoint : ℝ≥0} {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k F Gzero ambient
      p eta xi C b h)
    (hxi : xi < 1)
    (hCpoint : C / (1 - xi) ≤ Cpoint) (hCpointOne : 1 ≤ Cpoint)
    (i : Fin ell) (hk : k = i.castSucc) (hh : 3 ≤ h)
    (mSupply cutoff : ℕ)
    (hmSupply : (mSupply : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hcutoff : cutoff < mSupply)
    (hgapAlive : ((((W.U i.succ).card + 2 : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    (mLink DLink CLink : ℕ)
    (hlowerLink : (mLink + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupperLink : (1 + xi) *
      (p ^ 2 * eta * (W.U i.succ).card) ≤ (DLink : ℝ≥0))
    (hcodegreeLink : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (CLink : ℝ≥0)) :
    ∃ L : FiniteLaw (MasterStateOn V × (Sym2 V → Bool)),
      IsReserveStronglyWellDistributed L W k
          (fun z ↦ z.1.initial) (fun z ↦ z.1.later)
          (fun z ↦ reserveEdges z.1.graph (W.U i.succ) z.2)
          p 1 Cpoint b ∧
        L.SupportedOn (fun z ↦
          masterPointwiseGoodEvent W k F MasterStateOn.graph
            MasterStateOn.available MasterStateOn.initial MasterStateOn.later
            p eta xi h z.1) ∧
        L.SupportedOn (fun z ↦
          ReserveProtectedStageGood W i z.1.graph z.1.available
            (z.1.initial ∪ z.1.later) cutoff z.2) ∧
        L.SupportedOn (fun z ↦
          ReserveSampledLinkBoundsGood z.1.graph z.1.available
            (W.U i.succ) mLink DLink CLink z.2) ∧
        L.SupportedOn (fun z ↦ z.1.available ⊆ ambient) ∧
        L.SupportedOn (fun z ↦ z.1.initial ∪ z.1.later ⊆ ambient) ∧
        L.SupportedOn (fun z ↦
          CoversOriginalGraph Gzero z.1.graph z.1.initial z.1.later) ∧
        L.SupportedOn (fun z ↦ z.1.graph ≤ Gzero) ∧
        L.SupportedOn (fun z ↦
          GraphSupportedOn z.1.graph (W.U k : Set V)) ∧
        L.SupportedOn (fun z ↦ ∀ v : V,
          Even ((neighborsIn z.1.graph univ v).card)) ∧
        L.SupportedOn (fun z ↦
          reserveEdges z.1.graph (W.U i.succ) z.2 =
            crossingEdges z.1.graph (W.U i.succ)) := by
  obtain ⟨L, hreserve, hpoint, hstageGood, havailable, hselected,
      hcover, hsub, hgraphSupport, heven, hfull⟩ :=
    hmaster.exists_conditionedFullReserveStage hxi hCpoint hCpointOne i hk
      (by omega) mSupply cutoff hmSupply hcutoff hgapAlive
  have hstage : k.val ≤ i.val := by simpa [hk]
  have hlink : L.SupportedOn fun z ↦
      ReserveSampledLinkBoundsGood z.1.graph z.1.available
        (W.U i.succ) mLink DLink CLink z.2 := by
    intro z hz
    have hp := hpoint z hz
    have hGsupp : GraphSupportedOn z.1.graph
        (W.U i.castSucc : Set V) := by
      simpa only [hk] using hgraphSupport z hz
    exact hp.2.2.2.1.reserveSampledLinkBoundsGood_of_fullReserve
      hp.2.2.2.2.2.1 i hstage hGsupp hh z.2 (hfull z hz)
      mLink DLink CLink hlowerLink hupperLink hcodegreeLink
  exact ⟨L, hreserve, hpoint, hstageGood, hlink, havailable, hselected,
    hcover, hsub, hgraphSupport, heven, hfull⟩

end

end Erdos207
