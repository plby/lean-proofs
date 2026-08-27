/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterLawCompression
import ErdosProblems.Erdos207.ReserveStrongWellDistributed

/-!
# Conditioning and reserve sampling for a compressed stage

Every later master step starts in the same way: expose pointwise goodness on
the support of the current compressed law, absorb the conditioning factor in
a deterministic constant, and independently sample the crossing reserve.
This file packages that common boundary together with all deterministic
invariants needed by the preliminary kernel.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A supported predicate on the old compressed state remains supported after
adjoining any state-dependent finite kernel. -/
lemma FiniteLaw.SupportedOn.jointBind_fst
    {Omega Xi : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    {law : FiniteLaw Omega} {kernel : Omega → FiniteLaw Xi}
    {P : Omega → Prop} (hP : law.SupportedOn P) :
    (law.jointBind kernel).SupportedOn fun z ↦ P z.1 := by
  intro z hz
  exact hP z.1
    ((FiniteLaw.jointBind_mass_pos_iff law kernel z.1 z.2).mp hz).1

/-- Condition a compressed law on pointwise goodness, enlarge the resulting
multiplicative constant to a deterministic bound, and sample crossing reserve
edges.  The output law retains every old deterministic invariant and has the
reserve-aware strong product estimate. -/
theorem IsCompressedMasterLaw.exists_conditionedReserveStage
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C b Cbar reserveDensity : ℝ≥0} {h : ℕ}
    (hmaster : IsCompressedMasterLaw law W k F Gzero ambient
      p eta xi C b h)
    (hxi : xi < 1)
    (hCbar : C / (1 - xi) ≤ Cbar) (hCbarOne : 1 ≤ Cbar)
    (U : Finset V) (hreserveDensity : reserveDensity ≤ 1) :
    let Good : MasterStateOn V → Prop :=
      masterPointwiseGoodEvent W k F MasterStateOn.graph
        MasterStateOn.available MasterStateOn.initial MasterStateOn.later
        p eta xi h
    ∃ hpos : 0 < law.probability Good,
      let Lc := law.conditionOn Good hpos
      let reserveKernel : MasterStateOn V →
          FiniteLaw (Sym2 V → Bool) := fun state ↦
        reserveEdgeLaw (MasterStateOn.graph state) U reserveDensity
          hreserveDensity
      let Lr := Lc.jointBind reserveKernel
      IsCompressedMasterLaw Lc W k F Gzero ambient
          p eta xi Cbar b h ∧
        Lc.SupportedOn Good ∧
        IsReserveStronglyWellDistributed Lr W k
          (fun z ↦ MasterStateOn.initial z.1)
          (fun z ↦ MasterStateOn.later z.1)
          (fun z ↦ reserveEdges (MasterStateOn.graph z.1) U z.2)
          p reserveDensity Cbar b ∧
        Lr.SupportedOn (fun z ↦ Good z.1) ∧
        Lr.SupportedOn (fun z ↦
          MasterStateOn.available z.1 ⊆ ambient) ∧
        Lr.SupportedOn (fun z ↦
          MasterStateOn.initial z.1 ∪ MasterStateOn.later z.1 ⊆ ambient) ∧
        Lr.SupportedOn (fun z ↦
          CoversOriginalGraph Gzero (MasterStateOn.graph z.1)
            (MasterStateOn.initial z.1) (MasterStateOn.later z.1)) ∧
        Lr.SupportedOn (fun z ↦ MasterStateOn.graph z.1 ≤ Gzero) ∧
        Lr.SupportedOn (fun z ↦
          GraphSupportedOn (MasterStateOn.graph z.1) (W.U k : Set V)) ∧
        Lr.SupportedOn (fun z ↦ ∀ v : V,
          Even ((neighborsIn (MasterStateOn.graph z.1) univ v).card)) := by
  dsimp only
  let Good : MasterStateOn V → Prop :=
    masterPointwiseGoodEvent W k F MasterStateOn.graph
      MasterStateOn.available MasterStateOn.initial MasterStateOn.later
      p eta xi h
  have hpos : 0 < law.probability Good :=
    (tsub_pos_iff_lt.mpr hxi).trans_le hmaster.1.2.2
  refine ⟨hpos, ?_⟩
  let Lc := law.conditionOn Good hpos
  let reserveKernel : MasterStateOn V → FiniteLaw (Sym2 V → Bool) :=
    fun state ↦ reserveEdgeLaw (MasterStateOn.graph state) U reserveDensity
      hreserveDensity
  let Lr := Lc.jointBind reserveKernel
  have hconditioned := hmaster.conditionPointwise hxi
  have hcompressedExact : IsCompressedMasterLaw Lc W k F Gzero ambient
      p eta xi (C / law.probability Good) b h := by
    simpa only [Lc, Good, conditionedMasterLaw] using hconditioned.1
  have hprobLower : 1 - xi ≤ law.probability Good := hmaster.1.2.2
  have hdenom : 0 < 1 - xi := tsub_pos_iff_lt.mpr hxi
  have hfactor : C / law.probability Good ≤ Cbar := by
    exact (div_le_div_of_nonneg_left zero_le hdenom hprobLower).trans hCbar
  have hcompressed : IsCompressedMasterLaw Lc W k F Gzero ambient
      p eta xi Cbar b h := by
    refine ⟨⟨hcompressedExact.1.1,
      hcompressedExact.1.2.1.mono_factor hfactor,
      hcompressedExact.1.2.2⟩, hcompressedExact.2⟩
  have hGood : Lc.SupportedOn Good := by
    exact law.conditionOn_supported Good hpos
  have hreserve : IsReserveStronglyWellDistributed Lr W k
      (fun z ↦ MasterStateOn.initial z.1)
      (fun z ↦ MasterStateOn.later z.1)
      (fun z ↦ reserveEdges (MasterStateOn.graph z.1) U z.2)
      p reserveDensity Cbar b := by
    simpa only [Lr, reserveKernel] using
      hcompressed.1.2.1.jointBind_reserveEdges hCbarOne hreserveDensity
  refine ⟨hcompressed, hGood, hreserve,
    hGood.jointBind_fst, hcompressed.2.1.jointBind_fst,
    hcompressed.2.2.1.jointBind_fst,
    hcompressed.2.2.2.1.jointBind_fst,
    hcompressed.2.2.2.2.1.jointBind_fst,
    hcompressed.2.2.2.2.2.jointBind_fst, ?_⟩
  exact hcompressed.1.1.jointBind_fst

end

end Erdos207
