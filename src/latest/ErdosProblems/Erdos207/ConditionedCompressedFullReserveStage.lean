/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConditionedCompressedProtectedReserveStage

/-!
# Density-one reserve conditioning for a compressed stage

At reserve density one the crossing reserve is deterministic.  The generic
Bernoulli failure estimate is deliberately avoided: typicality proves the
common reserve-good event directly, and only the old pointwise event needs to
be conditioned on.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Condition a compressed law on pointwise goodness and attach the full
crossing reserve.  There is no second conditioning loss at density one. -/
theorem IsCompressedMasterLaw.exists_conditionedFullReserveStage
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C b Cpoint : ℝ≥0} {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k F Gzero ambient
      p eta xi C b h)
    (hxi : xi < 1)
    (hCpoint : C / (1 - xi) ≤ Cpoint) (hCpointOne : 1 ≤ Cpoint)
    (i : Fin ell) (hk : k = i.castSucc) (hh : 2 ≤ h)
    (mSupply cutoff : ℕ)
    (hmSupply : (mSupply : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hcutoff : cutoff < mSupply)
    (hgapAlive : ((((W.U i.succ).card + 2 : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card)) :
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
  let PointGood : MasterStateOn V → Prop :=
    masterPointwiseGoodEvent W k F MasterStateOn.graph
      MasterStateOn.available MasterStateOn.initial MasterStateOn.later
      p eta xi h
  have hpointPos : 0 < law.probability PointGood :=
    (tsub_pos_iff_lt.mpr hxi).trans_le hmaster.1.2.2
  let Lpoint := law.conditionOn PointGood hpointPos
  let reserveKernel : MasterStateOn V → FiniteLaw (Sym2 V → Bool) :=
    fun state ↦ reserveEdgeLaw state.graph (W.U i.succ) 1 (by norm_num)
  let L := Lpoint.jointBind reserveKernel
  have hconditioned := hmaster.conditionPointwise hxi
  have hcompressedExact : IsCompressedMasterLaw Lpoint W k F Gzero ambient
      p eta xi (C / law.probability PointGood) b h := by
    simpa only [Lpoint, PointGood, conditionedMasterLaw] using hconditioned.1
  have hdenPoint : 0 < 1 - xi := tsub_pos_iff_lt.mpr hxi
  have hpointFactor : C / law.probability PointGood ≤ Cpoint :=
    (div_le_div_of_nonneg_left zero_le hdenPoint hmaster.1.2.2).trans
      hCpoint
  have hcompressed : IsCompressedMasterLaw Lpoint W k F Gzero ambient
      p eta xi Cpoint b h := by
    refine ⟨⟨hcompressedExact.1.1,
      hcompressedExact.1.2.1.mono_factor hpointFactor,
      hcompressedExact.1.2.2⟩, hcompressedExact.2⟩
  have hreserve : IsReserveStronglyWellDistributed L W k
      (fun z ↦ z.1.initial) (fun z ↦ z.1.later)
      (fun z ↦ reserveEdges z.1.graph (W.U i.succ) z.2)
      p 1 Cpoint b := by
    simpa only [L, reserveKernel] using
      hcompressed.1.2.1.jointBind_reserveEdges hCpointOne (by norm_num)
  have hpointSupport : L.SupportedOn fun z ↦ PointGood z.1 :=
    (law.conditionOn_supported PointGood hpointPos).jointBind_fst
  have hmasses : ∀ z, 0 < L.mass z →
      0 < Lpoint.mass z.1 ∧ 0 < (reserveKernel z.1).mass z.2 := by
    intro z hz
    exact (FiniteLaw.jointBind_mass_pos_iff Lpoint reserveKernel z.1 z.2).mp
      (by simpa only [L] using hz)
  have hfull : L.SupportedOn fun z ↦
      reserveEdges z.1.graph (W.U i.succ) z.2 =
        crossingEdges z.1.graph (W.U i.succ) := by
    intro z hz
    have hm := hmasses z hz
    simpa only [reserveKernel] using
      reserveEdgeLaw_one_supported_full z.1.graph (W.U i.succ) z.2 hm.2
  have hstageGood : L.SupportedOn fun z ↦
      ReserveProtectedStageGood W i z.1.graph z.1.available
        (z.1.initial ∪ z.1.later) cutoff z.2 := by
    intro z hz
    have hm := hmasses z hz
    have hp := hpointSupport z hz
    have hGsupp : GraphSupportedOn z.1.graph
        (W.U i.castSucc : Set V) := by
      simpa only [hk] using hcompressed.2.2.2.2.2 z.1 hm.1
    have hstage : k.val ≤ i.val := by simpa [hk]
    exact hp.2.2.2.1.reserveProtectedStageGood_of_fullReserve
      hp.2.2.2.2.2.1 i hstage hGsupp hh z.2 (hfull z hz)
      mSupply cutoff hmSupply hcutoff hgapAlive
  refine ⟨L, hreserve, hpointSupport, hstageGood,
    hcompressed.2.1.jointBind_fst,
    hcompressed.2.2.1.jointBind_fst,
    hcompressed.2.2.2.1.jointBind_fst,
    hcompressed.2.2.2.2.1.jointBind_fst,
    hcompressed.2.2.2.2.2.jointBind_fst,
    hcompressed.1.1.jointBind_fst, hfull⟩

end

end Erdos207
