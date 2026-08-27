/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphDistribution
import ErdosProblems.Erdos207.MasterIterationConditioning
import ErdosProblems.Erdos207.MasterIterationUpdate
import ErdosProblems.Erdos207.MasterLawCompression

/-! # Master iteration with the compatible full-union residual law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def IsResidualMasterIterationGood
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G₀ : SimpleGraph V)
    (F : ForbiddenFamilyOn V) (G : Ω → SimpleGraph V) (A I D : Ω → TripleSystemOn V)
    (p eta xi C b : ℝ≥0) (h : ℕ) : Prop :=
  HasEvenStageGraphs L G ∧ IsResidualGraphStronglyWellDistributed L W k G₀ I D p C b ∧
    1 - xi ≤ L.probability (masterPointwiseGoodEvent W k F G A I D p eta xi h)

theorem IsResidualMasterIterationGood.conditionPointwise
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G₀ : SimpleGraph V}
    {F : ForbiddenFamilyOn V} {G : Ω → SimpleGraph V} {A I D : Ω → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsResidualMasterIterationGood L W k G₀ F G A I D p eta xi C b h)
    (hxi : xi < 1) :
    ∃ hpos : 0 < L.probability (masterPointwiseGoodEvent W k F G A I D p eta xi h),
      let Lc := L.conditionOn (masterPointwiseGoodEvent W k F G A I D p eta xi h) hpos
      IsResidualMasterIterationGood Lc W k G₀ F G A I D p eta xi
        (C / L.probability (masterPointwiseGoodEvent W k F G A I D p eta xi h)) b h ∧
      Lc.SupportedOn (masterPointwiseGoodEvent W k F G A I D p eta xi h) := by
  let Good := masterPointwiseGoodEvent W k F G A I D p eta xi h
  have hpos : 0 < L.probability Good := (tsub_pos_iff_lt.mpr hxi).trans_le hgood.2.2
  refine ⟨hpos, ?_⟩
  have hsupport := L.conditionOn_supported Good hpos
  refine ⟨⟨hgood.1.conditionOn hpos, hgood.2.1.conditionOn Good hpos, ?_⟩, hsupport⟩
  rw [(L.conditionOn Good hpos).probability_eq_one_of_supported Good hsupport]
  exact tsub_le_self

theorem IsResidualMasterIterationGood.map_packMasterState
    {Ω V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G₀ : SimpleGraph V}
    {F : ForbiddenFamilyOn V} {G : Ω → SimpleGraph V} {A I D : Ω → TripleSystemOn V}
    {p eta xi C b : ℝ≥0} {h : ℕ}
    (hgood : IsResidualMasterIterationGood L W k G₀ F G A I D p eta xi C b h) :
    IsResidualMasterIterationGood (L.map (packMasterState G A I D)) W k G₀ F
      MasterStateOn.graph MasterStateOn.available MasterStateOn.initial MasterStateOn.later
      p eta xi C b h := by
  let f := packMasterState G A I D
  refine ⟨hgood.1.map f (fun _ hω ↦ hω), ?_, ?_⟩
  · exact hgood.2.1.map f
  · rw [FiniteLaw.probability_map]
    exact hgood.2.2

theorem residualMasterIterationGood_of_probability_update
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k next : Fin (ell + 1)} {G₀ : SimpleGraph V}
    {F : ForbiddenFamilyOn V} {G : Ω → SimpleGraph V} {A I D M : Ω → TripleSystemOn V}
    {p eta xi xi' C b : ℝ≥0} {h : ℕ}
    (heven : HasEvenStageGraphs L (fun ω ↦ updatedStageGraph (G ω) (W.U next) (M ω)))
    (hstrong : IsResidualGraphStronglyWellDistributed L W next G₀ I (fun ω ↦ D ω ∪ M ω) p C b)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W k F G A I D p eta xi h))
    (hstep : L.SupportedOn fun ω ↦ IsMasterCoverStep F (G ω) (W.U next) (A ω) (I ω) (D ω) (M ω))
    (htyp : 1 - xi' ≤ L.probability (fun ω ↦ IsIterationTypical W next
      (updatedStageGraph (G ω) (W.U next) (M ω))
      (updatedStageAvailable F (W.U next) (A ω) (I ω) (D ω) (M ω)) p eta xi' h)) :
    IsResidualMasterIterationGood L W next G₀ F
      (fun ω ↦ updatedStageGraph (G ω) (W.U next) (M ω))
      (fun ω ↦ updatedStageAvailable F (W.U next) (A ω) (I ω) (D ω) (M ω))
      I (fun ω ↦ D ω ∪ M ω) p eta xi' C b h := by
  refine ⟨heven, hstrong, htyp.trans ?_⟩
  have hsupp : L.SupportedOn (fun ω ↦
      masterPointwiseGoodEvent W k F G A I D p eta xi h ω ∧
        IsMasterCoverStep F (G ω) (W.U next) (A ω) (I ω) (D ω) (M ω)) :=
    fun ω hω ↦ ⟨hold ω hω, hstep ω hω⟩
  apply L.probability_mono_of_supported hsupp
  intro ω hω htypical
  exact hω.1.updated hω.2 htypical

end

end Erdos207
