import ErdosProblems.Erdos421.DivisorWindowFinitePart
import ErdosProblems.Erdos421.FiniteLatticeMean

/-! # Weighted finite divisor windows and their uniform truncation error -/

namespace Erdos421

open MeasureTheory FourierTransform
open scoped SchwartzMap

theorem weighted_divisor_finite_part_mean (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hφ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (S : Finset ℕ) (a : ℕ → ℂ) {M H : ℕ} (hM : 0 < M)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    {Y : ℝ} (hY : 0 < Y) {u v : ℝ} (huv : u ≤ v) :
    (∫ x in u..v, ‖∑ m ∈ S, a m * divisorWindowFinitePart φ Y H x m‖ ^ 2) ≤
      (v - u + 16 * M ^ 2 * Real.log (4 * Real.pi * H * M ^ 2 + 2)) *
        (2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y) := by
  let J := (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0
  let T := S ×ˢ J
  have hT : ∀ w ∈ T, 0 < w.1 ∧ w.1 ≤ M := by
    intro w hw
    exact hS w.1 (Finset.mem_product.mp hw).1
  have haT : ∀ w ∈ T, ‖a w.1‖ ≤ 1 := by
    intro w hw
    exact ha w.1 (Finset.mem_product.mp hw).1
  have hzero : ∀ w ∈ T, w.2 ≠ 0 := by
    intro w hw
    exact (Finset.mem_erase.mp (Finset.mem_product.mp hw).2).1
  have hspan : ∀ w ∈ T, |(w.2 : ℝ) / w.1| ≤ H := by
    intro w hw
    have hmR : (0 : ℝ) < w.1 := by exact_mod_cast (hT w hw).1
    have hm1 : (1 : ℝ) ≤ w.1 := by exact_mod_cast (hT w hw).1
    have hh := Finset.mem_Icc.mp (Finset.mem_of_mem_erase (Finset.mem_product.mp hw).2)
    have habs : |(w.2 : ℝ)| ≤ (H : ℝ) := by exact_mod_cast abs_le.mpr hh
    rw [abs_div, abs_of_pos hmR]
    apply (div_le_iff₀ hmR).mpr
    nlinarith [show (0 : ℝ) ≤ H from Nat.cast_nonneg H]
  have hb := finite_lattice_mean_square φ hφ T a hM hT haT hzero
    (Nat.cast_nonneg H) hY hspan huv
  have heq (x : ℝ) : (∑ m ∈ S, a m * divisorWindowFinitePart φ Y H x m) =
      ∑ w ∈ T, ((a w.1 / (w.1 : ℂ)) * 𝓕 φ (Y * (w.2 : ℝ) / w.1)) *
        oscillatoryPhase (2 * Real.pi * ((w.2 : ℝ) / w.1)) x := by
    dsimp only [T]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro m hm
    rw [divisorWindowFinitePart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [fourier_divisor_oscillatoryPhase]
    ring
  simpa only [← heq] using hb

theorem weighted_divisor_window_truncation_error (φ : 𝓢(ℝ, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C)
    (S : Finset ℕ) (a : ℕ → ℂ) {M H : ℕ}
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    {Y : ℝ} (hY : 0 < Y) (hH : 0 < H) (x : ℝ) :
    ‖(∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
        (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))) -
      ∑ m ∈ S, a m * divisorWindowFinitePart φ Y H x m‖ ≤
        2 * C * M ^ 2 / (Y ^ 2 * H) := by
  have hsub : S ⊆ Finset.Icc 1 M := fun m hm ↦ Finset.mem_Icc.mpr (hS m hm)
  have hcard : S.card ≤ M := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ M := by exact_mod_cast hcard
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ m ∈ S, ‖a m * ((additiveDivisorWindow φ Y x m -
        (m : ℂ)⁻¹ * (∫ z : ℝ, φ z)) - divisorWindowFinitePart φ Y H x m)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, 2 * C * M / (Y ^ 2 * H) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      have hb := divisorWindowFinitePart_error φ hC hφ hY x (hS m hm).1 hH
      have hmR : (m : ℝ) ≤ M := by exact_mod_cast (hS m hm).2
      calc
        _ ≤ 1 * (2 * C * m / (Y ^ 2 * H)) :=
          mul_le_mul (ha m hm) hb (norm_nonneg _) (by norm_num)
        _ ≤ _ := by
          rw [one_mul]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmR (by positivity)) (by positivity)
    _ = S.card * (2 * C * M / (Y ^ 2 * H)) := by simp
    _ ≤ (M : ℝ) * (2 * C * M / (Y ^ 2 * H)) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = _ := by ring

end Erdos421
