import ErdosProblems.Erdos67b.ElliottHarmonicMass
import ErdosProblems.Erdos67b.LogTranslation

/-! # Trimming a fixed initial segment from the Elliott logarithmic window -/

open scoped BigOperators
open Finset

namespace Erdos67b

def elliottTrimmedLower (X W L₀ : ℕ) : ℕ := max L₀ (X / W + 1)

theorem elliottTrimmedWindow_subset {X W : ℕ} (hW : 0 < W) (L₀ : ℕ) :
    Icc (elliottTrimmedLower X W L₀) X ⊆ elliottLogWindow X W := by
  rw [elliottLogWindow_eq_Ioc hW]
  intro n hn
  obtain ⟨hnlo, hnhi⟩ := mem_Icc.1 hn
  have hlo := (le_max_right L₀ (X / W + 1)).trans hnlo
  exact mem_Ioc.2 ⟨by omega, hnhi⟩

theorem elliottTrimmedWindow_omitted_subset {X W : ℕ} (hW : 0 < W) (L₀ : ℕ) :
    elliottLogWindow X W \ Icc (elliottTrimmedLower X W L₀) X ⊆ range L₀ := by
  rw [elliottLogWindow_eq_Ioc hW]
  intro n hn
  obtain ⟨hn, hnnot⟩ := mem_sdiff.1 hn
  obtain ⟨hnlo, hnhi⟩ := mem_Ioc.1 hn
  simp only [mem_Icc, elliottTrimmedLower, max_le_iff] at hnnot
  exact mem_range.2 (by omega)

theorem elliottTrimmedLower_geometry {X W L₀ : ℕ}
    (hW : 4 ≤ W) (hWX : W ≤ X) (hX : 2 * L₀ ≤ X) :
    0 < elliottTrimmedLower X W L₀ ∧
      L₀ ≤ elliottTrimmedLower X W L₀ ∧
      2 * elliottTrimmedLower X W L₀ ≤ X := by
  have hN : 1 ≤ X / W := Nat.div_pos hWX (by omega)
  have hmul : 4 * (X / W) ≤ X :=
    (Nat.mul_le_mul_right _ hW).trans (by simpa [mul_comm] using Nat.div_mul_le_self X W)
  have hnext : 2 * (X / W + 1) ≤ X := by omega
  unfold elliottTrimmedLower
  refine ⟨by omega, le_max_left _ _, ?_⟩
  rcases le_total L₀ (X / W + 1) with h | h
  · simpa only [max_eq_right h] using hnext
  · simpa only [max_eq_left h] using hX

theorem norm_elliottWindow_trim_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X W : ℕ} (hW : 0 < W) (L₀ : ℕ) (g : ℕ → E)
    (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1) :
    ‖(∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ • g n) -
      ∑ n ∈ Icc (elliottTrimmedLower X W L₀) X, (n : ℝ)⁻¹ • g n‖ ≤ L₀ := by
  classical
  let S := elliottLogWindow X W \ Icc (elliottTrimmedLower X W L₀) X
  rw [← sum_sdiff (elliottTrimmedWindow_subset hW L₀), add_sub_cancel_right]
  change ‖∑ n ∈ S, (n : ℝ)⁻¹ • g n‖ ≤ L₀
  have hterm : ∀ n ∈ S, ‖(n : ℝ)⁻¹ • g n‖ ≤ 1 := by
    intro n hn
    have hnpos := (mem_elliottLogWindow.1 (mem_sdiff.1 hn).1).1
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have hw : (n : ℝ)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnr
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
    exact mul_le_one₀ hw (by positivity) (hg n hnpos)
  calc
    _ ≤ ∑ n ∈ S, ‖(n : ℝ)⁻¹ • g n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, (1 : ℝ) := sum_le_sum hterm
    _ = S.card := by simp
    _ ≤ L₀ := by
      have hc : S.card ≤ L₀ := by
        simpa only [card_range] using
          card_le_card (elliottTrimmedWindow_omitted_subset (X := X) hW L₀)
      exact_mod_cast hc

theorem elliottTrimmedMass_bounds {X W L₀ : ℕ}
    (hW : 0 < W) (hWX : W ≤ X)
    (hlog : 2 * ((L₀ : ℝ) + 1) ≤ Real.log W) :
    Real.log W / 2 ≤ (logProbMassNN (elliottTrimmedLower X W L₀) X : ℝ) ∧
      (logProbMassNN (elliottTrimmedLower X W L₀) X : ℝ) ≤ 2 * Real.log W := by
  have hmass := elliottLogMass_bounds hW hWX
  have herr := norm_elliottWindow_trim_error (X := X) hW L₀ (fun _ ↦ (1 : ℝ)) (by simp)
  simp only [smul_eq_mul, mul_one, Real.norm_eq_abs] at herr
  change |elliottLogMass X W - ∑ n ∈ Icc (elliottTrimmedLower X W L₀) X, (n : ℝ)⁻¹| ≤ L₀ at herr
  rw [← logProbMassNN_coe_eq_Icc_sum] at herr
  have hupper : (logProbMassNN (elliottTrimmedLower X W L₀) X : ℝ) ≤ elliottLogMass X W := by
    rw [logProbMassNN_coe_eq_Icc_sum]
    exact sum_le_sum_of_subset_of_nonneg (elliottTrimmedWindow_subset hW L₀)
      (fun n _ _ ↦ by positivity)
  constructor
  · have := (abs_le.1 herr).2
    linarith
  · linarith [Nat.cast_nonneg (α := ℝ) L₀]

end Erdos67b
