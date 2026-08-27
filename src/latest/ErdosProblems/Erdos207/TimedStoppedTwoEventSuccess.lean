/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteStoppedKernel

/-! # Two-event success extraction from one frozen finite law -/

namespace Erdos207.FiniteLaw

noncomputable section

theorem timedStopped_probability_early_good_le_other_failure
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω) (active P Q : ℕ → Ω → Prop) (x₀ : Ω)
    (hactive : ∀ z, 0 < (timedStoppedProcessLaw n K active x₀).mass z →
      P z.1.1 z.2 → Q z.1.1 z.2 → active z.1.1 z.2) :
    (timedStoppedProcessLaw n K active x₀).probability (fun z ↦ z.1.1 ≠ n ∧ P z.1.1 z.2) ≤
      (timedStoppedProcessLaw n K active x₀).probability (fun z ↦ ¬ Q z.1.1 z.2) := by
  let L := timedStoppedProcessLaw n K active x₀
  apply L.probability_mono_of_supported (R := fun z ↦ 0 < L.mass z) (fun _ h ↦ h)
  intro z hz hbad hQ
  have hterminal := timedStoppedProcessLaw_supported_terminal n K active x₀ z hz
  exact (hterminal.resolve_left hbad.1) (hactive z hz hbad.2 hQ)

theorem exists_timedStopped_horizon_of_two_failure_bounds
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω) (active P Q : ℕ → Ω → Prop) (x₀ : Ω)
    (epsilonP epsilonQ : ℝ)
    (hP : ((timedStoppedProcessLaw n K active x₀).probability (fun z ↦ ¬ P z.1.1 z.2) : ℝ) ≤ epsilonP)
    (hQ : ((timedStoppedProcessLaw n K active x₀).probability (fun z ↦ ¬ Q z.1.1 z.2) : ℝ) ≤ epsilonQ)
    (hsmall : epsilonP + epsilonQ < 1)
    (hactive : ∀ z, 0 < (timedStoppedProcessLaw n K active x₀).mass z →
      P z.1.1 z.2 → Q z.1.1 z.2 → active z.1.1 z.2) :
    ∃ z, 0 < (timedStoppedProcessLaw n K active x₀).mass z ∧ z.1.1 = n ∧
      P z.1.1 z.2 ∧ Q z.1.1 z.2 := by
  classical
  let L := timedStoppedProcessLaw n K active x₀
  let bad : TimedState Ω n → Prop := fun z ↦ ¬ P z.1.1 z.2 ∨ ¬ Q z.1.1 z.2
  have hor : (L.probability bad : ℝ) ≤
      (L.probability (fun z ↦ ¬ P z.1.1 z.2) : ℝ) +
        (L.probability (fun z ↦ ¬ Q z.1.1 z.2) : ℝ) := by
    exact_mod_cast L.probability_or_le (fun z ↦ ¬ P z.1.1 z.2) (fun z ↦ ¬ Q z.1.1 z.2)
  have hbad : (L.probability bad : ℝ) < 1 :=
    (hor.trans (add_le_add hP hQ)).trans_lt hsmall
  have hexists : ∃ z, 0 < L.mass z ∧ P z.1.1 z.2 ∧ Q z.1.1 z.2 := by
    by_contra hnone
    have hsupp : L.SupportedOn bad := by
      intro z hz
      by_cases hp : P z.1.1 z.2
      · exact Or.inr fun hq ↦ hnone ⟨z, hz, hp, hq⟩
      · exact Or.inl hp
    rw [L.probability_eq_one_of_supported bad hsupp] at hbad
    norm_num at hbad
  obtain ⟨z, hmass, hp, hq⟩ := hexists
  have hztime := (timedStoppedProcessLaw_supported_terminal n K active x₀ z hmass).resolve_right
    (not_not_intro (hactive z hmass hp hq))
  exact ⟨z, hmass, hztime, hp, hq⟩

end

end Erdos207.FiniteLaw
