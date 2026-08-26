import ErdosProblems.Erdos421.OneSidedSchwartzWindow

/-! # The positive plateau in the normalized one-sided window -/

namespace Erdos421

open Complex MeasureTheory
open scoped SchwartzMap

noncomputable def oneSidedWindowHeight : ℝ := 1 / ∫ x : ℝ, oneSidedBump x

theorem oneSidedWindowHeight_pos : 0 < oneSidedWindowHeight :=
  one_div_pos.mpr (oneSidedBump.integral_pos (μ := volume))

theorem oneSidedSchwartzWindow_plateau {x : ℝ}
    (hx : x ∈ Set.Icc (-3 / 4 : ℝ) (-1 / 4)) :
    oneSidedSchwartzWindow x = (oneSidedWindowHeight : ℂ) := by
  have hball : x ∈ Metric.closedBall (-1 / 2 : ℝ) oneSidedBump.rIn := by
    change x ∈ Metric.closedBall (-1 / 2 : ℝ) (1 / 4)
    rw [Metric.mem_closedBall, Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  rw [oneSidedSchwartzWindow_apply, ContDiffBump.normed_def,
    oneSidedBump.one_of_mem_closedBall hball]
  rfl

theorem oneSided_unit_window_re (S : Finset ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    (schwartzDirichletWindow S (fun _ ↦ 1) 1
      (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y).re =
      ∑ n ∈ S, (n : ℝ)⁻¹ * δ⁻¹ * (oneSidedSchwartzWindow ((y - Real.log n) / δ)).re := by
  rw [schwartzDirichletWindow_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [normalizedSchwartzScale_apply, Complex.real_smul]
  simp only [one_mul, Real.rpow_neg_one, Complex.mul_re, ofReal_re, ofReal_im,
    zero_mul, sub_zero]
  ring

theorem oneSided_unit_window_re_nonneg (S : Finset ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    0 ≤ (schwartzDirichletWindow S (fun _ ↦ 1) 1
      (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y).re := by
  rw [oneSided_unit_window_re S hδ y]
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (inv_pos.mpr hδ).le)
    (oneSidedSchwartzWindow_real_nonneg _).2

theorem oneSided_unit_window_re_lower_bound (S T : Finset ℕ) (hTS : T ⊆ S)
    {δ V y : ℝ} (hδ : 0 < δ) (hV : 0 < V)
    (hT : ∀ n ∈ T, 0 < n ∧ (n : ℝ) ≤ V ∧
      (y - Real.log n) / δ ∈ Set.Icc (-3 / 4 : ℝ) (-1 / 4)) :
    (T.card : ℝ) * oneSidedWindowHeight / (δ * V) ≤
      (schwartzDirichletWindow S (fun _ ↦ 1) 1
        (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y).re := by
  rw [oneSided_unit_window_re S hδ y]
  have hterm : ∀ n ∈ T, oneSidedWindowHeight / (δ * V) ≤
      (n : ℝ)⁻¹ * δ⁻¹ * (oneSidedSchwartzWindow ((y - Real.log n) / δ)).re := by
    intro n hn
    obtain ⟨hnp, hnV, hplateau⟩ := hT n hn
    rw [oneSidedSchwartzWindow_plateau hplateau, ofReal_re]
    have hinv : 1 / V ≤ 1 / (n : ℝ) :=
      (div_le_div_iff₀ hV (Nat.cast_pos.mpr hnp)).mpr (by simpa only [one_mul] using hnV)
    calc
      _ = (1 / V) * δ⁻¹ * oneSidedWindowHeight := by ring
      _ ≤ (n : ℝ)⁻¹ * δ⁻¹ * oneSidedWindowHeight := by
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hinv (inv_pos.mpr hδ).le) oneSidedWindowHeight_pos.le
        simpa only [one_div] using hm
  calc
    _ = ∑ _n ∈ T, oneSidedWindowHeight / (δ * V) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ n ∈ T, (n : ℝ)⁻¹ * δ⁻¹ *
        (oneSidedSchwartzWindow ((y - Real.log n) / δ)).re := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hTS (fun n _ _ ↦
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (inv_pos.mpr hδ).le)
        (oneSidedSchwartzWindow_real_nonneg _).2)

end Erdos421
