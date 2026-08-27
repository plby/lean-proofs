/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualMasterIteration

/-! # Fixed-state compression with the corrected residual distribution -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The fixed-state invariant carried by the finite vortex induction. -/
def IsResidualCompressedMasterLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (law : FiniteLaw (MasterStateOn V))
    (W : Vortex V ell) (k : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (Gzero : SimpleGraph V)
    (ambient : TripleSystemOn V)
    (p eta xi C b : ℝ≥0) (h : ℕ) : Prop :=
  IsResidualMasterIterationGood law W k Gzero F
      MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later
      p eta xi C b h ∧
    law.SupportedOn (fun state ↦
      MasterStateOn.available state ⊆ ambient) ∧
    law.SupportedOn (fun state ↦
      MasterStateOn.initial state ∪ MasterStateOn.later state ⊆ ambient) ∧
    law.SupportedOn (fun state ↦
      CoversOriginalGraph Gzero (MasterStateOn.graph state)
        (MasterStateOn.initial state) (MasterStateOn.later state)) ∧
    law.SupportedOn (fun state ↦ MasterStateOn.graph state ≤ Gzero) ∧
    law.SupportedOn (fun state ↦
      GraphSupportedOn (MasterStateOn.graph state) (W.U k : Set V))

/-- Compress a law together with all five deterministic induction clauses. -/
theorem IsResidualMasterIterationGood.compress
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsResidualMasterIterationGood law W k Gzero F G A I D
      p eta xi C b h)
    (havailable : law.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega ↦ G omega ≤ Gzero)
    (hsupport : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (W.U k : Set V)) :
    IsResidualCompressedMasterLaw (law.map (packMasterState G A I D))
      W k F Gzero ambient p eta xi C b h := by
  refine ⟨hgood.map_packMasterState, ?_,
    hselected.map_packMasterState_selected,
    hcover.map_packMasterState_coverage, ?_, ?_⟩
  exact havailable.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)
  exact hsub.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)
  exact hsupport.map (packMasterState G A I D)
    (fun omega homega ↦ by simpa using homega)

/-- A completed cover step preserves the five deterministic induction
invariants; compressing its joint law therefore produces the next fixed-state
master law. -/
theorem compressResidualMasterUpdate
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {kernel : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {Gzero : SimpleGraph V}
    {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {M : Omega × Xi → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsResidualMasterIterationGood (law.jointBind kernel) W next Gzero F
      (fun z ↦ updatedStageGraph (G z.1) (W.U next) (M z))
      (fun z ↦ updatedStageAvailable F (W.U next)
        (A z.1) (I z.1) (D z.1) (M z))
      (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ M z)
      p eta xi C b h)
    (hstep : (law.jointBind kernel).SupportedOn fun z ↦
      IsMasterCoverStep F (G z.1) (W.U next)
        (A z.1) (I z.1) (D z.1) (M z))
    (havailable : law.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega ↦ G omega ≤ Gzero) :
    IsResidualCompressedMasterLaw
      ((law.jointBind kernel).map (packMasterState
        (fun z ↦ updatedStageGraph (G z.1) (W.U next) (M z))
        (fun z ↦ updatedStageAvailable F (W.U next)
          (A z.1) (I z.1) (D z.1) (M z))
        (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ M z)))
      W next F Gzero ambient p eta xi C b h := by
  let joint := law.jointBind kernel
  have havailableJoint : joint.SupportedOn fun z ↦ A z.1 ⊆ ambient := by
    have hbind := havailable.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _havailable ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hselectedJoint : joint.SupportedOn fun z ↦
      I z.1 ∪ D z.1 ⊆ ambient := by
    have hbind := hselected.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _hselected ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hcoverJoint : joint.SupportedOn fun z ↦
      CoversOriginalGraph Gzero (G z.1) (I z.1) (D z.1) := by
    have hbind := hcover.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _hcover ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hnewAvailable : joint.SupportedOn fun z ↦
      updatedStageAvailable F (W.U next)
          (A z.1) (I z.1) (D z.1) (M z) ⊆ ambient := by
    intro z hz
    exact (updatedStageAvailable_subset F (W.U next)
      (A z.1) (I z.1) (D z.1) (M z)).trans
        (havailableJoint z hz)
  have hnewSelected : joint.SupportedOn fun z ↦
      I z.1 ∪ (D z.1 ∪ M z) ⊆ ambient := by
    intro z hz T hT
    rcases mem_union.mp hT with hTI | hTDM
    · exact hselectedJoint z hz (mem_union_left (D z.1) hTI)
    · rcases mem_union.mp hTDM with hTD | hTM
      · exact hselectedJoint z hz (mem_union_right (I z.1) hTD)
      · exact havailableJoint z hz ((hstep z hz).selected hTM)
  have hnewCover : joint.SupportedOn fun z ↦
      CoversOriginalGraph Gzero
        (updatedStageGraph (G z.1) (W.U next) (M z))
        (I z.1) (D z.1 ∪ M z) := by
    intro z hz
    exact (hcoverJoint z hz).updated (hstep z hz)
  have hnewSupport : joint.SupportedOn fun z ↦
      GraphSupportedOn
        (updatedStageGraph (G z.1) (W.U next) (M z))
        (W.U next : Set V) := by
    intro z _hz
    exact updatedStageGraph_supported (G z.1) (W.U next) (M z)
  have hsubJoint : joint.SupportedOn fun z ↦ G z.1 ≤ Gzero := by
    have hbind := hsub.jointBind (K := kernel)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _hsub ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (hbind z hz).1
  have hnewSub : joint.SupportedOn fun z ↦
      updatedStageGraph (G z.1) (W.U next) (M z) ≤ Gzero := by
    intro z hz
    exact (updatedStageGraph_le (G z.1) (W.U next) (M z)).trans
      (hsubJoint z hz)
  exact hgood.compress hnewAvailable hnewSelected hnewCover hnewSub hnewSupport

theorem exists_ksssOutsidePacking_of_finalResidualMasterIterationGood
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsResidualMasterIterationGood law W k
      (graphDifference (SimpleGraph.completeGraph V) H)
      (absorberErdosForbiddenConfigurationsOn q B) G A I D
      p eta xi C b h)
    (hxi : xi < 1)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ outsideAvailableTriangles H B)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hsupport : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (X : Set V)) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let Good : Omega → Prop := fun omega ↦
    IsMasterStagePointwiseGood W k
      (absorberErdosForbiddenConfigurationsOn q B)
      (G omega) (A omega) (I omega) (D omega) p eta xi h
  have hprob : 0 < law.probability Good := by
    exact (tsub_pos_iff_lt.mpr hxi).trans_le hgood.2.2
  obtain ⟨omega, homega, hmass⟩ :=
    law.exists_of_probability_pos_with_mass hprob
  let P := I omega ∪ D omega
  have hPselected : P ⊆ outsideAvailableTriangles H B :=
    hselected omega hmass
  have hPsupport : GraphSupportedOn
      (graphDifference (leaveGraph P) H) (X : Set V) := by
    intro u v huv
    have hleave := leaveGraph_adj.mp huv.1
    have horiginal :
        (graphDifference (SimpleGraph.completeGraph V) H).Adj u v := by
      refine ⟨?_, huv.1.ne, huv.2.2⟩
      simpa using huv.1.ne
    have hcoveredOrG := hcover omega hmass horiginal
    rw [SimpleGraph.sup_adj] at hcoveredOrG
    rcases hcoveredOrG with hcovered | hG
    · exact (hleave.2 hcovered).elim
    · exact hsupport omega hmass hG
  refine ⟨P, hasKSSSOutsidePacking_of_maximal ?_ hPselected ?_ hPsupport⟩
  · exact homega.2.1
  · exact homega.2.2.1

/-- At the terminal vortex level, a compressed iteration-good law is already
an outside packing: its support invariant says that the current remainder is
entirely contained in the flexible set. -/
theorem IsResidualCompressedMasterLaw.exists_ksssOutsidePacking
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {q : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B : TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hmaster : IsResidualCompressedMasterLaw law W k
      (absorberErdosForbiddenConfigurationsOn q B)
      (graphDifference (SimpleGraph.completeGraph V) H)
      (outsideAvailableTriangles H B) p eta xi C b h)
    (hX : W.U k = X) (hxi : xi < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  apply exists_ksssOutsidePacking_of_finalResidualMasterIterationGood
    hmaster.1 hxi hmaster.2.2.1 hmaster.2.2.2.1
  intro state hmass
  simpa only [hX] using hmaster.2.2.2.2.2 state hmass

/-- Conditioning preserves every deterministic compressed-state invariant. -/
theorem IsResidualCompressedMasterLaw.conditionPointwise
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell}
    {k : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hmaster : IsResidualCompressedMasterLaw law W k F Gzero ambient p eta xi C b h)
    (hxi : xi < 1) :
    let Good := masterPointwiseGoodEvent W k F
      MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later p eta xi h
    ∃ hpos : 0 < law.probability Good,
      let Lc := law.conditionOn Good hpos
      IsResidualCompressedMasterLaw Lc W k F Gzero ambient p eta xi
        (C / law.probability Good) b h ∧ Lc.SupportedOn Good := by
  dsimp only
  obtain ⟨hpos, hgood, hsupport⟩ := hmaster.1.conditionPointwise hxi
  exact ⟨hpos, ⟨hgood, hmaster.2.1.conditionOn hpos, hmaster.2.2.1.conditionOn hpos,
    hmaster.2.2.2.1.conditionOn hpos, hmaster.2.2.2.2.1.conditionOn hpos,
    hmaster.2.2.2.2.2.conditionOn hpos⟩, hsupport⟩

end

end Erdos207
