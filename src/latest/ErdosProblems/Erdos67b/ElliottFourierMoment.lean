import ErdosProblems.Erdos67b.ElliottFourierAdapter
import ErdosProblems.Erdos67b.ElliottTrimmedWindow

/-! # The normalized Fourier first moment on the trimmed logarithmic law -/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

theorem sum_weighted_modulated_norm_eq {H : ℕ} (hH : 0 < H)
    (f : ℕ → ℂ) (X W : ℕ) (α : ℝ) :
    (∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ * ‖modulatedShortSum f n H α‖) =
      H * logAverageModulatedShortSum f X W H α := by
  rw [logAverageModulatedShortSum_eq hH, mul_sum]
  apply sum_congr rfl
  intro n _
  dsimp only [harmonicWeight]
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

theorem logProb_fourier_firstMoment_of_MRT
    {X W H L₀ : ℕ} (hW : 0 < W) (hH : 0 < H)
    (hM : 0 < (logProbMassNN (elliottTrimmedLower X W L₀) X : ℝ))
    (hMlo : Real.log W / 2 ≤ (logProbMassNN (elliottTrimmedLower X W L₀) X : ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ) (f : ℕ → ℂ) (T : ℕ) (t : ℤ)
    (hfirst : logAverageModulatedShortSum f X W H ((t : ℝ) / T) ≤ δ * Real.log W) :
    logProbExpectation (elliottTrimmedLower X W L₀) X (fun n ↦
      ‖blockFourier T (finiteSequenceBlock f H n) t‖) ≤ 2 * δ * H := by
  rw [logProbExpectation_eq_mass_inv_smul_sum]
  simp only [smul_eq_mul, norm_blockFourier_finiteSequenceBlock]
  let M : ℝ := logProbMassNN (elliottTrimmedLower X W L₀) X
  have hsum : (∑ n ∈ Icc (elliottTrimmedLower X W L₀) X,
      (n : ℝ)⁻¹ * ‖modulatedShortSum f n H ((t : ℝ) / T)‖) ≤
      H * (δ * Real.log W) := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (elliottTrimmedWindow_subset hW L₀)
      (fun n _ _ ↦ by positivity))
    rw [sum_weighted_modulated_norm_eq hH]
    exact mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg H)
  change M⁻¹ * _ ≤ _
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hM).2
  apply hsum.trans
  have h := mul_le_mul_of_nonneg_left hMlo
    (show 0 ≤ 2 * δ * (H : ℝ) by positivity)
  nlinarith only [h]

theorem norm_shiftedLogCorrelation_le_trimmed
    {X W : ℕ} (hW : 0 < W) (L₀ h : ℕ) (f : ℕ → ℂ)
    (hf : ∀ n, 0 < n → ‖f n‖ = 1) :
    ‖shiftedLogCorrelation f h X W‖ ≤
      ‖∑ n ∈ Icc (elliottTrimmedLower X W L₀) X,
        (n : ℝ)⁻¹ • (f n * conj (f (n + h)))‖ + L₀ := by
  have herr := norm_elliottWindow_trim_error (X := X) hW L₀
    (fun n ↦ f n * conj (f (n + h))) (by
      intro n hn
      rw [norm_mul, Complex.norm_conj, hf n hn, hf (n + h) (by omega)]
      norm_num)
  have heq : shiftedLogCorrelation f h X W =
      ∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ • (f n * conj (f (n + h))) := by
    simp only [shiftedLogCorrelation, harmonicWeight, Complex.real_smul, mul_assoc]
  rw [heq]
  apply (norm_le_norm_add_norm_sub
    (∑ n ∈ Icc (elliottTrimmedLower X W L₀) X,
      (n : ℝ)⁻¹ • (f n * conj (f (n + h)))) _).trans
  apply add_le_add le_rfl
  simpa only [norm_sub_rev] using herr

end

end Erdos67b
