/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualRawLinkJointUpdate

/-! # Conditioning actual simultaneous-link success without losing the master certificate -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualGraphStronglyWellDistributed.condition_rawLink_masterCover
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {next : Fin (ell+1)} {Gamma : SimpleGraph V}
    {U : Finset V} {F : ForbiddenFamilyOn V} {G : Ω → SimpleGraph V}
    {A I D R : Ω → TripleSystemOn V} {result : Ω → TripleSystemOn V × TripleSystemOn V}
    {links : Ω → {x : V // x ∉ U} → BipartiteLink V} {p C b error : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W next Gamma I
      (fun omega ↦ (D omega ∪ R omega) ∪ (result omega).2) p C b)
    (hstate : L.SupportedOn fun omega ↦ IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega) (R omega) (links omega))
    (hstruct : L.SupportedOn fun omega ↦ IsSampledLinkJointOutcome F (A omega)
      (I omega ∪ (D omega ∪ R omega)) (links omega) (result omega))
    (hfailure : L.probability (fun omega ↦ ¬ ∀ o, CoversBipartiteLink (links omega o) (result omega).2) ≤ error)
    (herror : error < 1) :
    let Success := fun omega ↦ ∀ o, CoversBipartiteLink (links omega o) (result omega).2
    ∃ hpos : 0 < L.probability Success,
      1-error ≤ L.probability Success ∧
      IsResidualGraphStronglyWellDistributed (L.conditionOn Success hpos) W next Gamma I
        (fun omega ↦ D omega ∪ (R omega ∪ (result omega).2)) p (C/(1-error)) b ∧
      (L.conditionOn Success hpos).SupportedOn fun omega ↦
        IsMasterCoverStep F (G omega) U (A omega) (I omega) (D omega) (R omega ∪ (result omega).2) := by
  dsimp only
  let Success := fun omega ↦ ∀ o, CoversBipartiteLink (links omega o) (result omega).2
  have hlower : 1-error ≤ L.probability Success := by
    have hb := hfailure
    rw [L.probability_not] at hb
    exact tsub_le_iff_tsub_le.mp hb
  have hden : 0 < 1-error := tsub_pos_iff_lt.mpr herror
  have hpos : 0 < L.probability Success := hden.trans_le hlower
  refine ⟨hpos, hlower, ?_, ?_⟩
  · have hc := (hstrong.conditionOn Success hpos).mono
      (div_le_div_of_nonneg_left zero_le hden hlower) le_rfl
    simpa only [union_assoc] using hc
  · have hstate' := hstate.conditionOn hpos
    have hstruct' := hstruct.conditionOn hpos
    have hsuccess := L.conditionOn_supported Success hpos
    intro omega hmass
    exact (hstruct' omega hmass).masterCoverStep (hstate' omega hmass) (hsuccess omega hmass)

theorem FiniteLaw.condition_success_probability_not_le
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (Success Good : Ω → Prop)
    (error failure : ℝ≥0) (herror : error < 1) (hpos : 0 < L.probability Success)
    (hlower : 1-error ≤ L.probability Success)
    (hbad : L.probability (fun omega ↦ ¬ Good omega) ≤ failure) :
    (L.conditionOn Success hpos).probability (fun omega ↦ ¬ Good omega) ≤ failure/(1-error) := by
  calc
    _ ≤ L.probability (fun omega ↦ ¬ Good omega)/L.probability Success := L.conditionOn_probability_le Success _ hpos
    _ ≤ failure/L.probability Success := div_le_div_of_nonneg_right hbad zero_le
    _ ≤ failure/(1-error) := div_le_div_of_nonneg_left zero_le (tsub_pos_iff_lt.mpr herror) hlower

end

end Erdos207
