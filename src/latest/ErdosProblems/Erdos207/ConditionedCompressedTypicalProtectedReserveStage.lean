/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConditionedCompressedProtectedReserveStage
import ErdosProblems.Erdos207.ReserveSampledLinkConcentration

/-!
# Conditioning a compressed stage on all sparse-reserve estimates

Besides supplying the two cover-down processes, the sampled crossing reserve
must leave every outside link with controlled degree and codegree.  This file
intersects those requirements before conditioning, so the binomial estimates
are applied to the original independent reserve law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The common reserve event used by the sparse-reserve transition. -/
def ReserveProtectedTypicalStageGood
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (G : SimpleGraph V) (A P : TripleSystemOn V) (cutoff : ℕ)
    (mLink DLink CLink : ℕ) (bits : Sym2 V → Bool) : Prop :=
  ReserveProtectedStageGood W i G A P cutoff bits ∧
    ReserveSampledLinkBoundsGood G A (W.U i.succ)
      mLink DLink CLink bits

theorem probability_not_reserveProtectedTypicalStageGood_le_of_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (G : SimpleGraph V) (A P : TripleSystemOn V) (cutoff : ℕ)
    (mLink DLink CLink : ℕ) (r : ℝ≥0) (hr : r ≤ 1)
    (epsilonProtected epsilonLink : ℝ≥0)
    (hProtected : (reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ ReserveProtectedStageGood W i G A P cutoff bits) ≤
        epsilonProtected)
    (hLink : (reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ ReserveSampledLinkBoundsGood G A (W.U i.succ)
        mLink DLink CLink bits) ≤ epsilonLink) :
    (reserveEdgeLaw G (W.U i.succ) r hr).probability
        (fun bits ↦ ¬ ReserveProtectedTypicalStageGood W i G A P cutoff
          mLink DLink CLink bits) ≤
      epsilonProtected + epsilonLink := by
  let L := reserveEdgeLaw G (W.U i.succ) r hr
  have hmono : L.probability
      (fun bits ↦ ¬ ReserveProtectedTypicalStageGood W i G A P cutoff
        mLink DLink CLink bits) ≤
      L.probability (fun bits ↦
        ¬ ReserveProtectedStageGood W i G A P cutoff bits ∨
          ¬ ReserveSampledLinkBoundsGood G A (W.U i.succ)
            mLink DLink CLink bits) := by
    apply L.probability_mono
    intro bits hbad
    simpa only [ReserveProtectedTypicalStageGood, not_and_or] using hbad
  exact hmono.trans ((L.probability_or_le _ _).trans
    (add_le_add hProtected hLink))

/-- Condition a compressed master law simultaneously on pointwise goodness,
the two cover-down reserve requirements, and all sampled-link degree and
codegree requirements. -/
theorem IsCompressedMasterLaw.exists_conditionedTypicalProtectedReserveStage
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
    (mLink DLink CLink : ℕ) (epsilonLink : ℝ≥0)
    (hfailureLink : ∀ state : MasterStateOn V,
      reserveSampledLinkFailureTail V state.available (W.U i.succ)
        reserveDensity mLink DLink CLink ≤ epsilonLink)
    (hepsilonReserve : epsilonSupply + epsilonAlive + epsilonLink < 1)
    (hCreserve : Cpoint /
      (1 - (epsilonSupply + epsilonAlive + epsilonLink)) ≤ Creserve) :
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
    fun z ↦ ReserveProtectedTypicalStageGood W i z.1.graph z.1.available
      (z.1.initial ∪ z.1.later) cutoff mLink DLink CLink z.2
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
        ¬ ReserveProtectedTypicalStageGood W i state.graph state.available
          (state.initial ∪ state.later) cutoff mLink DLink CLink bits) ≤
        epsilonSupply + epsilonAlive + epsilonLink := by
    intro state hmass
    have hp := (law.conditionOn_supported PointGood hpointPos) state hmass
    have htyp := hp.2.2.2.1
    have htri := hp.2.2.2.2.2.1
    have hGsupp : GraphSupportedOn state.graph
        (W.U i.castSucc : Set V) := by
      simpa only [hk] using hcompressed.2.2.2.2.2 state hmass
    have hstage : k.val ≤ i.val := by simpa [hk]
    have hProtected : (reserveKernel state).probability (fun bits ↦
        ¬ ReserveProtectedStageGood W i state.graph state.available
          (state.initial ∪ state.later) cutoff bits) ≤
        epsilonSupply + epsilonAlive := by
      simpa only [reserveKernel] using
        htyp.reserveEdgeLaw_probability_not_reserveProtectedStageGood_le
          htri i hstage hGsupp hh reserveDensity hreserveDensity
          mSupply cutoff hmSupply hcutoff epsilonSupply
          (hfailureSupply state) mAlive hgapAlive epsilonAlive
          (hfailureAlive state)
    have hLink : (reserveKernel state).probability (fun bits ↦
        ¬ ReserveSampledLinkBoundsGood state.graph state.available
          (W.U i.succ) mLink DLink CLink bits) ≤ epsilonLink := by
      exact (by
        simpa only [reserveKernel] using
          (reserveEdgeLaw_probability_not_sampledLinkBoundsGood_le
            state.graph state.available (W.U i.succ) htri reserveDensity
              hreserveDensity mLink DLink CLink).trans
                (hfailureLink state))
    exact probability_not_reserveProtectedTypicalStageGood_le_of_parts
      W i state.graph state.available (state.initial ∪ state.later)
      cutoff mLink DLink CLink reserveDensity hreserveDensity
      (epsilonSupply + epsilonAlive) epsilonLink hProtected hLink
  have hlower : 1 - (epsilonSupply + epsilonAlive + epsilonLink) ≤
      J.probability ReserveGood := by
    exact Lpoint.one_sub_le_jointBind_probability_on_support reserveKernel
      (fun state bits ↦ ReserveProtectedTypicalStageGood W i state.graph
        state.available (state.initial ∪ state.later) cutoff
          mLink DLink CLink bits)
      (epsilonSupply + epsilonAlive + epsilonLink) hbad
  have hreservePos : 0 < J.probability ReserveGood :=
    (tsub_pos_iff_lt.mpr hepsilonReserve).trans_le hlower
  let L := J.conditionOn ReserveGood hreservePos
  have hreserveJ : IsReserveStronglyWellDistributed J W k
      (fun z ↦ z.1.initial) (fun z ↦ z.1.later)
      (fun z ↦ reserveEdges z.1.graph (W.U i.succ) z.2)
      p reserveDensity Cpoint b := by
    simpa only [J, reserveKernel] using
      hcompressed.1.2.1.jointBind_reserveEdges hCpointOne hreserveDensity
  have hdenReserve : 0 < 1 -
      (epsilonSupply + epsilonAlive + epsilonLink) :=
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
    intro z hz
    exact (J.conditionOn_supported ReserveGood hreservePos z hz).1
  have hlinkSupport : L.SupportedOn fun z ↦
      ReserveSampledLinkBoundsGood z.1.graph z.1.available
        (W.U i.succ) mLink DLink CLink z.2 := by
    intro z hz
    exact (J.conditionOn_supported ReserveGood hreservePos z hz).2
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
    hstageSupport, hlinkSupport,
    hcompressed.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.2.2.1.jointBind_fst.conditionOn hreservePos,
    hcompressed.2.2.2.2.2.jointBind_fst.conditionOn hreservePos,
    hcompressed.1.1.jointBind_fst.conditionOn hreservePos,
    hfullJ.conditionOn hreservePos⟩

end

end Erdos207
