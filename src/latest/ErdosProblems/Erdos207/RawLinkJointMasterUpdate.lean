/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawLinkJointConditioning
import ErdosProblems.Erdos207.ResidualMasterIteration

/-! # Closing the master-law bookkeeping after actual joint-link success -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem residualMasterIterationGood_of_rawLink_joint_success
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k next : Fin (ell+1)} {Gamma : SimpleGraph V}
    {F : ForbiddenFamilyOn V} {G : Ω → SimpleGraph V}
    {A I D R : Ω → TripleSystemOn V} {result : Ω → TripleSystemOn V × TripleSystemOn V}
    {links : Ω → {x : V // x ∉ W.U next} → BipartiteLink V}
    {p eta xi xi' C b error failure : ℝ≥0} {h : ℕ}
    (hstrong : IsResidualGraphStronglyWellDistributed L W next Gamma I
      (fun omega ↦ (D omega ∪ R omega) ∪ (result omega).2) p C b)
    (heven : HasEvenStageGraphs L G)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W k F G A I D p eta xi h))
    (hstate : L.SupportedOn fun omega ↦ IsIntermediateLinkState (G omega) (W.U next)
      (A omega) (I omega) (D omega) (R omega) (links omega))
    (hstruct : L.SupportedOn fun omega ↦ IsSampledLinkJointOutcome F (A omega)
      (I omega ∪ (D omega ∪ R omega)) (links omega) (result omega))
    (hcoverage : L.probability (fun omega ↦ ¬ ∀ o, CoversBipartiteLink (links omega o) (result omega).2) ≤ error)
    (herror : error < 1)
    (hfuture : L.probability (fun omega ↦ ¬ IsIterationTypical W next
      (updatedStageGraph (G omega) (W.U next) (R omega ∪ (result omega).2))
      (updatedStageAvailable F (W.U next) (A omega) (I omega) (D omega) (R omega ∪ (result omega).2))
      p eta xi' h) ≤ failure)
    (hbudget : failure ≤ xi'*(1-error)) :
    let Success := fun omega ↦ ∀ o, CoversBipartiteLink (links omega o) (result omega).2
    ∃ hpos : 0 < L.probability Success,
      1-error ≤ L.probability Success ∧
      IsResidualMasterIterationGood (L.conditionOn Success hpos) W next Gamma F
        (fun omega ↦ updatedStageGraph (G omega) (W.U next) (R omega ∪ (result omega).2))
        (fun omega ↦ updatedStageAvailable F (W.U next) (A omega) (I omega) (D omega) (R omega ∪ (result omega).2))
        I (fun omega ↦ D omega ∪ (R omega ∪ (result omega).2)) p eta xi' (C/(1-error)) b h := by
  dsimp only
  let Success := fun omega ↦ ∀ o, CoversBipartiteLink (links omega o) (result omega).2
  let Typical := fun omega ↦ IsIterationTypical W next
    (updatedStageGraph (G omega) (W.U next) (R omega ∪ (result omega).2))
    (updatedStageAvailable F (W.U next) (A omega) (I omega) (D omega) (R omega ∪ (result omega).2)) p eta xi' h
  obtain ⟨hpos, hlower, hstrong', hstep⟩ := hstrong.condition_rawLink_masterCover hstate hstruct hcoverage herror
  have hbad : (L.conditionOn Success hpos).probability (fun omega ↦ ¬ Typical omega) ≤ xi' := by
    apply (L.condition_success_probability_not_le Success Typical error failure herror hpos hlower hfuture).trans
    exact (div_le_iff₀ (tsub_pos_iff_lt.mpr herror)).mpr hbudget
  have htyp : 1-xi' ≤ (L.conditionOn Success hpos).probability Typical := by
    rw [(L.conditionOn Success hpos).probability_not Typical] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  have hold' := hold.conditionOn hpos
  have heven' := heven.conditionOn hpos
  refine ⟨hpos, hlower, residualMasterIterationGood_of_probability_update ?_ hstrong' hold' hstep htyp⟩
  intro omega hmass
  exact (hstep omega hmass).updated_even (heven' omega hmass) (hold' omega hmass).2.2.2.2.2.1

end

end Erdos207
