import ErdosProblems.Erdos421.LogCorrelationBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Cancellation for logarithmic sums in the quadratic-to-cubic range -/

namespace Erdos421

theorem cubic_scale_inverse_sqrt_bound {M R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hRM : R ≤ M) (hMR : M ^ 2 ≤ R ^ 3) :
    M / Real.sqrt (R ^ 3 / M) ≤ R := by
  have hMR₂ : M ≤ R ^ 2 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    have hm := mul_le_mul_of_nonneg_right hRM (sq_nonneg R)
    nlinarith
  have hMR₅ : M ^ 3 ≤ R ^ 5 := by
    calc
      _ = M ^ 2 * M := by ring
      _ ≤ R ^ 3 * R ^ 2 := mul_le_mul hMR hMR₂ hM.le (by positivity)
      _ = _ := by ring
  have hs : 0 < Real.sqrt (R ^ 3 / M) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ R ^ 3 / M)
  apply (div_le_iff₀ hs).mpr
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, hsq]
  calc
    _ ≤ R ^ 5 / M := (le_div_iff₀ hM).mpr (by nlinarith)
    _ = _ := by ring

theorem logarithmic_cubic_correlation_bound {M N h : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (hh : 0 < h) {R : ℝ} (hR : 0 < R) (hRM : R ≤ M) (hMR : (M : ℝ) ^ 2 ≤ R ^ 3)
    (hhR : (h : ℝ) ≤ M / R) :
    ‖finiteCorrelation (fun n ↦ oscillatoryPhase (Real.log (M + n : ℕ)) (R ^ 3)) N h‖ ≤
      640 * R := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  by_cases hhN : h ≤ N
  · have hb := logarithmic_finiteCorrelation_bound hM hN hh hhN (pow_pos hR 3)
    have heff : R ^ 3 * h / M ≤ R ^ 2 := by
      have hm := (le_div_iff₀ hR).mp hhR
      apply (div_le_iff₀ hMp).mpr
      have hm₂ := mul_le_mul_of_nonneg_left hm (sq_nonneg R)
      nlinarith
    have hsupper : Real.sqrt (R ^ 3 * h / M) ≤ R :=
      (Real.sqrt_le_iff).mpr ⟨hR.le, heff⟩
    have hefflower : R ^ 3 / M ≤ R ^ 3 * h / M := by
      apply div_le_div_of_nonneg_right _ hMp.le
      nlinarith [pow_nonneg hR.le 3]
    have hslower : Real.sqrt (R ^ 3 / M) ≤ Real.sqrt (R ^ 3 * h / M) :=
      Real.sqrt_le_sqrt hefflower
    have hinv := div_le_div_of_nonneg_left hMp.le
      (Real.sqrt_pos.mpr (by positivity : 0 < R ^ 3 / M)) hslower
    have hsecond := hinv.trans (cubic_scale_inverse_sqrt_bound hMp hR hRM hMR)
    linarith
  · have hzero : N - h = 0 := by omega
    simp only [finiteCorrelation, hzero, Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity

theorem logarithmicSum_cubic_scale_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    {R : ℝ} (hR1 : 1 ≤ R) (hRM : R ≤ M) (hMR : (M : ℝ) ^ 2 ≤ R ^ 3) :
    ‖logarithmicSum M N (R ^ 3)‖ ^ 2 ≤ 1300 * M * R := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hR : 0 < R := by linarith
  let H := ⌊(M : ℝ) / R⌋₊
  have hH : 0 < H := by
    have hq : 1 ≤ (M : ℝ) / R := (one_le_div hR).mpr hRM
    exact (Nat.one_le_floor_iff _).mpr hq
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hHq : (H : ℝ) ≤ M / R := Nat.floor_le (by positivity)
  have hHM : H ≤ M := Nat.floor_le_of_le ((div_le_iff₀ hR).mpr (by nlinarith))
  have hfloor : (M : ℝ) ≤ 2 * H * R := by
    have hlo := Nat.lt_floor_add_one ((M : ℝ) / R)
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hq : (M : ℝ) / R ≤ 2 * H := by dsimp only [H] at *; linarith
    exact (div_le_iff₀ hR).mp hq
  have hcorr : ∀ h, 0 < h → h < H →
      ‖finiteCorrelation (fun n ↦ oscillatoryPhase (Real.log (M + n : ℕ)) (R ^ 3)) N h‖ ≤
        640 * R := by
    intro h hh hhH
    have hhH' : (h : ℝ) ≤ H := by exact_mod_cast hhH.le
    exact logarithmic_cubic_correlation_bound hM hN hh hR hRM hMR (hhH'.trans hHq)
  have hbound := vanDerCorput_uniform_length_bound
    (fun n ↦ oscillatoryPhase (Real.log (M + n : ℕ)) (R ^ 3)) hH hN hHM
    (by positivity : 0 ≤ 640 * R) (fun n _ ↦ by simp) hcorr
  have hdiv : 2 * (M : ℝ) ^ 2 / H ≤ 4 * M * R := by
    apply (div_le_iff₀ hHp).mpr
    have hm := mul_le_mul_of_nonneg_left hfloor (by positivity : (0 : ℝ) ≤ 2 * M)
    nlinarith
  change ‖logarithmicSum M N (R ^ 3)‖ ^ 2 ≤ _ at hbound
  nlinarith [mul_nonneg hMp.le hR.le]

/-- A third-derivative estimate in the range where the second-derivative
bound no longer supplies cancellation. -/
theorem logarithmicSum_third_derivative_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    {τ : ℝ} (hlo : (M : ℝ) ^ 2 ≤ τ) (hhi : τ ≤ (M : ℝ) ^ 3) :
    ‖logarithmicSum M N τ‖ ^ 2 ≤ 1300 * M * τ ^ ((3 : ℝ)⁻¹) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hτ : 0 < τ := (sq_pos_of_pos hMp).trans_le hlo
  let R := τ ^ ((3 : ℝ)⁻¹)
  have hc : R ^ 3 = τ := Real.rpow_inv_natCast_pow hτ.le (by decide : (3 : ℕ) ≠ 0)
  have hR1 : 1 ≤ R := by
    have hτ1 : 1 ≤ τ := by nlinarith
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hτ1
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
    simpa only [Real.one_rpow] using h
  have hRM : R ≤ M := by
    have h := Real.rpow_le_rpow hτ.le hhi (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
    have heq : ((M : ℝ) ^ (3 : ℕ)) ^ ((3 : ℝ)⁻¹) = M :=
      Real.pow_rpow_inv_natCast hMp.le (by decide : (3 : ℕ) ≠ 0)
    rw [heq] at h
    exact h
  have h := logarithmicSum_cubic_scale_bound hM hN hR1 hRM (by rwa [hc])
  rwa [hc] at h

end Erdos421
