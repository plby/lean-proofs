/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredStepBounds

/-! # Reducing indexed two-sided band failure to signed centered deviations -/

namespace Erdos207

open Finset

theorem band_failure_centered_deviation
    (y y₀ e e₀ a : ℝ) (hmargin : |y₀| + a ≤ e₀) (hbad : e < |y|) :
    a ≤ (y - e) - (y₀ - e₀) ∨ a ≤ (-y - e) - (-y₀ - e₀) := by
  have hp := le_abs_self y₀
  have hm := neg_abs_le y₀
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy] at hbad
    exact Or.inl (by linarith)
  · rw [abs_of_neg hy] at hbad
    exact Or.inr (by linarith)

theorem probability_band_failure_le_two_tails
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (tracked : Ω → Prop)
    (y e : Ω → ℝ) (y₀ e₀ a epsilonPlus epsilonMinus : ℝ)
    (hmargin : ∀ ω, 0 < L.mass ω → tracked ω → |y₀| + a ≤ e₀)
    (hplus : (L.probability (fun ω ↦ tracked ω ∧ a ≤ (y ω - e ω) - (y₀ - e₀)) : ℝ) ≤ epsilonPlus)
    (hminus : (L.probability (fun ω ↦ tracked ω ∧ a ≤ (-y ω - e ω) - (-y₀ - e₀)) : ℝ) ≤ epsilonMinus) :
    (L.probability (fun ω ↦ tracked ω ∧ e ω < |y ω|) : ℝ) ≤ epsilonPlus + epsilonMinus := by
  classical
  have hsub : ∀ ω, 0 < L.mass ω → tracked ω ∧ e ω < |y ω| →
      (tracked ω ∧ a ≤ (y ω - e ω) - (y₀ - e₀)) ∨
        (tracked ω ∧ a ≤ (-y ω - e ω) - (-y₀ - e₀)) := by
    intro ω hmass h
    rcases band_failure_centered_deviation (y ω) y₀ (e ω) e₀ a (hmargin ω hmass h.1) h.2 with hp | hm
    · exact Or.inl ⟨h.1, hp⟩
    · exact Or.inr ⟨h.1, hm⟩
  have hm := (L.probability_mono_of_supported (R := fun ω ↦ 0 < L.mass ω)
    (fun _ h ↦ h) hsub).trans
    (L.probability_or_le (fun ω ↦ tracked ω ∧ a ≤ (y ω - e ω) - (y₀ - e₀))
      (fun ω ↦ tracked ω ∧ a ≤ (-y ω - e ω) - (-y₀ - e₀)))
  have hmr : (L.probability (fun ω ↦ tracked ω ∧ e ω < |y ω|) : ℝ) ≤
      (L.probability (fun ω ↦ tracked ω ∧ a ≤ (y ω - e ω) - (y₀ - e₀)) : ℝ) +
        (L.probability (fun ω ↦ tracked ω ∧ a ≤ (-y ω - e ω) - (-y₀ - e₀)) : ℝ) := by
    exact_mod_cast hm
  exact hmr.trans (add_le_add hplus hminus)

theorem probability_indexed_band_failure_le_two_tails
    {Ω I : Type*} [Fintype Ω] [Fintype I] (L : FiniteLaw Ω)
    (tracked : I → Ω → Prop) (y e : I → Ω → ℝ)
    (y₀ e₀ a epsilonPlus epsilonMinus : I → ℝ)
    (hmargin : ∀ i ω, 0 < L.mass ω → tracked i ω → |y₀ i| + a i ≤ e₀ i)
    (hplus : ∀ i, (L.probability
      (fun ω ↦ tracked i ω ∧ a i ≤ (y i ω - e i ω) - (y₀ i - e₀ i)) : ℝ) ≤ epsilonPlus i)
    (hminus : ∀ i, (L.probability
      (fun ω ↦ tracked i ω ∧ a i ≤ (-y i ω - e i ω) - (-y₀ i - e₀ i)) : ℝ) ≤ epsilonMinus i) :
    (L.probability (fun ω ↦ ∃ i, tracked i ω ∧ e i ω < |y i ω|) : ℝ) ≤
      ∑ i, (epsilonPlus i + epsilonMinus i) := by
  classical
  have hu := L.probability_exists_le (univ : Finset I)
    (fun i ω ↦ tracked i ω ∧ e i ω < |y i ω|)
  simp only [mem_univ, true_and] at hu
  have hur : (L.probability (fun ω ↦ ∃ i, tracked i ω ∧ e i ω < |y i ω|) : ℝ) ≤
      ∑ i, (L.probability (fun ω ↦ tracked i ω ∧ e i ω < |y i ω|) : ℝ) := by
    exact_mod_cast hu
  apply hur.trans
  apply sum_le_sum
  intro i _
  exact probability_band_failure_le_two_tails L (tracked i) (y i) (e i)
    (y₀ i) (e₀ i) (a i) (epsilonPlus i) (epsilonMinus i) (hmargin i) (hplus i) (hminus i)

end Erdos207
