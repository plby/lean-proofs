/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConditionedCompressedReserveStage
import ErdosProblems.Erdos207.FiniteJointConditioning
import ErdosProblems.Erdos207.ReserveProtectedStageGood

/-!
# Pointwise and protected-reserve conditioning of a compressed stage

A later master step first conditions the compressed law on its pointwise
event, samples the crossing reserve, and then conditions on the common event
that supplies internal wedges while leaving every protected preliminary pair
alive.  This theorem packages both reciprocal losses and lifts all old
deterministic invariants to the twice-conditioned law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsCompressedMasterLaw.exists_conditionedProtectedReserveStage
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C b Cpoint reserveDensity Creserve : ℝ≥0}
    {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k F Gzero ambient
      p eta xi C b h)
    (hxi : xi < 1)
    (hCpoint : C / (1 - xi) ≤ Cpoint) (hCpointOne : 1 ≤ Cpoint)
    (i : Fin ell) (hk : k = i.castSucc) (hh : 2 ≤ h)
    (hreserveDensity : reserveDensity ≤ 1)
    (mSupply cutoff : ℕ)
    (hmSupply : (mSupply : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hcutoff : (cutoff : ℝ) ≤
      ((reserveDensity ^ 2 : ℝ≥0) : ℝ) * mSupply / 4)
    (epsilonSupply : ℝ≥0)
    (hfailureSupply : ∀ state : MasterStateOn V,
      ((internalOuterEdges state.graph (W.U i.succ)).card : ℝ) *
        Real.exp (-(((reserveDensity ^ 2 : ℝ≥0) : ℝ) * mSupply) / 4) ≤
          epsilonSupply)
    (mAlive : ℕ)
    (hgapAlive : ((((W.U i.succ).card + 2 + mAlive : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    (epsilonAlive : ℝ≥0)
    (hfailureAlive : ∀ state : MasterStateOn V,
      ((outerGraphEdges state.graph (W.U i.succ)).card : ℝ≥0) *
          reserveDensity ^ mAlive ≤ epsilonAlive)
    (hepsilonReserve : epsilonSupply + epsilonAlive < 1)
    (hCreserve : Cpoint / (1 - (epsilonSupply + epsilonAlive)) ≤ Creserve) :
    ∃ L : FiniteLaw (MasterStateOn V × (Sym2 V → Bool)),
      IsReserveStronglyWellDistributed L W k
          (fun z ↦ z.1.initial) (fun z ↦ z.1.later)
          (fun z ↦ reserveEdges z.1.graph (W.U i.succ) z.2)
          p reserveDensity Creserve b ∧
        L.SupportedOn (fun z ↦
          masterPointwiseGoodEvent W k F MasterStateOn.graph
            MasterStateOn.available MasterStateOn.initial MasterStateOn.later
            p eta xi h z.1) ∧
        L.SupportedOn (fun z ↦
          ReserveProtectedStageGood W i z.1.graph z.1.available
            (z.1.initial ∪ z.1.later) cutoff z.2) ∧
        L.SupportedOn (fun z ↦ z.1.available ⊆ ambient) ∧
        L.SupportedOn (fun z ↦ z.1.initial ∪ z.1.later ⊆ ambient) ∧
        L.SupportedOn (fun z ↦
          CoversOriginalGraph Gzero z.1.graph z.1.initial z.1.later) ∧
        L.SupportedOn (fun z ↦ z.1.graph ≤ Gzero) ∧
        L.SupportedOn (fun z ↦
          GraphSupportedOn z.1.graph (W.U k : Set V)) ∧
        L.SupportedOn (fun z ↦ ∀ v : V,
          Even ((neighborsIn z.1.graph univ v).card)) ∧
        L.SupportedOn (fun z ↦ reserveDensity = 1 →
          reserveEdges z.1.graph (W.U i.succ) z.2 =
            crossingEdges z.1.graph (W.U i.succ)) := by
  let PointGood : MasterStateOn V → Prop :=
    masterPointwiseGoodEvent W k F MasterStateOn.graph
      MasterStateOn.available MasterStateOn.initial MasterStateOn.later
      p eta xi h
  have hpointPos : 0 < law.probability PointGood :=
    (tsub_pos_iff_lt.mpr hxi).trans_le hmaster.1.2.2
  let Lpoint := law.conditionOn PointGood hpointPos
  let reserveKernel : MasterStateOn V → FiniteLaw (Sym2 V → Bool) :=
    fun state ↦ reserveEdgeLaw state.graph (W.U i.succ) reserveDensity
      hreserveDensity
  let J := Lpoint.jointBind reserveKernel
  let ReserveGood : MasterStateOn V × (Sym2 V → Bool) → Prop :=
    fun z ↦ ReserveProtectedStageGood W i z.1.graph z.1.available
      (z.1.initial ∪ z.1.later) cutoff z.2
  have hconditioned := hmaster.conditionPointwise hxi
  have hcompressedExact : IsCompressedMasterLaw Lpoint W k F Gzero ambient
      p eta xi (C / law.probability PointGood) b h := by
    simpa only [Lpoint, PointGood, conditionedMasterLaw] using hconditioned.1
  have hdenPoint : 0 < 1 - xi := tsub_pos_iff_lt.mpr hxi
  have hpointFactor : C / law.probability PointGood ≤ Cpoint := by
    exact (div_le_div_of_nonneg_left zero_le hdenPoint hmaster.1.2.2).trans
      hCpoint
  have hcompressed : IsCompressedMasterLaw Lpoint W k F Gzero ambient
      p eta xi Cpoint b h := by
    refine ⟨⟨hcompressedExact.1.1,
      hcompressedExact.1.2.1.mono_factor hpointFactor,
      hcompressedExact.1.2.2⟩, hcompressedExact.2⟩
  have hbad : ∀ state, 0 < Lpoint.mass state →
      (reserveKernel state).probability (fun bits ↦
        ¬ ReserveProtectedStageGood W i state.graph state.available
          (state.initial ∪ state.later) cutoff bits) ≤
        epsilonSupply + epsilonAlive := by
    intro state hmass
    have hp := (law.conditionOn_supported PointGood hpointPos) state hmass
    have htyp := hp.2.2.2.1
    have htri := hp.2.2.2.2.2.1
    have hGsupp : GraphSupportedOn state.graph
        (W.U i.castSucc : Set V) :=
      by simpa only [hk] using hcompressed.2.2.2.2.2 state hmass
    have hstage : k.val ≤ i.val := by simpa [hk]
    simpa only [reserveKernel] using
      htyp.reserveEdgeLaw_probability_not_reserveProtectedStageGood_le
        htri i hstage hGsupp hh reserveDensity hreserveDensity
        mSupply cutoff hmSupply hcutoff epsilonSupply
        (hfailureSupply state)
        mAlive hgapAlive epsilonAlive
        (hfailureAlive state)
  have hlower : 1 - (epsilonSupply + epsilonAlive) ≤
      J.probability ReserveGood := by
    exact Lpoint.one_sub_le_jointBind_probability_on_support reserveKernel
      (fun state bits ↦ ReserveProtectedStageGood W i state.graph
        state.available (state.initial ∪ state.later) cutoff bits)
      (epsilonSupply + epsilonAlive) hbad
  have hreservePos : 0 < J.probability ReserveGood :=
    (tsub_pos_iff_lt.mpr hepsilonReserve).trans_le hlower
  let L := J.conditionOn ReserveGood hreservePos
  have hreserveJ : IsReserveStronglyWellDistributed J W k
      (fun z ↦ z.1.initial) (fun z ↦ z.1.later)
      (fun z ↦ reserveEdges z.1.graph (W.U i.succ) z.2)
      p reserveDensity Cpoint b := by
    simpa only [J, reserveKernel] using
      hcompressed.1.2.1.jointBind_reserveEdges hCpointOne hreserveDensity
  have hdenReserve : 0 < 1 - (epsilonSupply + epsilonAlive) :=
    tsub_pos_iff_lt.mpr hepsilonReserve
  have hfactor : Cpoint / J.probability ReserveGood ≤ Creserve :=
    (div_le_div_of_nonneg_left zero_le hdenReserve hlower).trans hCreserve
  have hreserve : IsReserveStronglyWellDistributed L W k
      (fun z ↦ z.1.initial) (fun z ↦ z.1.later)
      (fun z ↦ reserveEdges z.1.graph (W.U i.succ) z.2)
      p reserveDensity Creserve b :=
    (hreserveJ.conditionOn ReserveGood hreservePos).mono_factor hfactor
  have hpointSupportJ : J.SupportedOn fun z ↦ PointGood z.1 :=
    (law.conditionOn_supported PointGood hpointPos).jointBind_fst
  have hstageSupport : L.SupportedOn fun z ↦
      ReserveProtectedStageGood W i z.1.graph z.1.available
        (z.1.initial ∪ z.1.later) cutoff z.2 := by
    exact J.conditionOn_supported ReserveGood hreservePos
  have hfullJ : J.SupportedOn fun z ↦ reserveDensity = 1 →
      reserveEdges z.1.graph (W.U i.succ) z.2 =
        crossingEdges z.1.graph (W.U i.succ) := by
    intro z hz hrate
    have hmasses := (FiniteLaw.jointBind_mass_pos_iff Lpoint reserveKernel
      z.1 z.2).mp hz
    subst reserveDensity
    simpa only [reserveKernel] using
      reserveEdgeLaw_one_supported_full z.1.graph (W.U i.succ) z.2
        hmasses.2
  refine ⟨L, hreserve, hpointSupportJ.conditionOn hreservePos,
    hstageSupport,
    hcompressed.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.2.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.2.2.2.jointBind_fst.conditionOn hreservePos,
    hcompressed.1.1.jointBind_fst.conditionOn hreservePos,
    hfullJ.conditionOn hreservePos⟩

end

end Erdos207
