import ErdosProblems.Erdos421.CutoffMassArithmetic
import ErdosProblems.Erdos421.ClippedCutoffMass

/-! # The total cutoff error has negligible logarithmic mass -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem clipped_cutoff_cubic_log_saving {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ W B : ℕ, (X : ℝ) ^ β ≤ W → 3 * X ≤ B → B ≤ 4 * X →
      ((primePartitionCount X : ℝ)⁻¹ + 2 / (W : ℝ)) * (harmonic B : ℝ) ^ 3 ≤
        τ / (Real.log X) ^ 2 := by
  have hloglarge : ∀ᶠ X : ℕ in atTop, max 1 (Real.log 4) ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 1, hloglarge,
    constant_inverse_log_saving 27 2 (by positivity : 0 < τ / 2),
    inverse_log_above_inverse_power hβ (by positivity : 0 < τ / 108) 5]
    with X hX hlog hfirstsave hsmall
  intro W B hW hB hBX
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hBpos : 0 < B := by omega
  have hlog1 : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
  have hlog4 : Real.log 4 ≤ Real.log X := (le_max_right _ _).trans hlog
  have hL : 0 < Real.log X := by linarith
  have hb := clipped_cutoff_mass_numeric hXp hW hBpos (by exact_mod_cast hBX) hlog1 hlog4
  have hfirst : 27 / (Real.log X) ^ (3 : ℕ) ≤ τ / 2 / (Real.log X) ^ (2 : ℕ) := by
    simpa only [show (-2 - 1 : ℝ) = -(3 : ℝ) by norm_num,
      Real.rpow_neg hL.le, Real.rpow_ofNat, div_eq_mul_inv] using hfirstsave
  norm_num only [Real.rpow_ofNat] at hsmall
  have hsecond : 54 * (X : ℝ) ^ (-β) * (Real.log X) ^ (3 : ℕ) ≤
      τ / 2 / (Real.log X) ^ (2 : ℕ) := by
    calc
      _ ≤ 54 * (τ / 108 / (Real.log X) ^ (5 : ℕ)) * (Real.log X) ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (by norm_num))
          (pow_nonneg hL.le _)
      _ = _ := by field_simp; ring
  apply hb.trans
  calc
    _ ≤ 27 / (Real.log X) ^ (3 : ℕ) +
        54 * (X : ℝ) ^ (-β) * (Real.log X) ^ (3 : ℕ) := by
      exact add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hL 3)
        (pow_le_pow_right₀ hlog1 (by decide : 3 ≤ 7))) le_rfl
    _ ≤ τ / 2 / (Real.log X) ^ (2 : ℕ) + τ / 2 / (Real.log X) ^ (2 : ℕ) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

theorem clipped_errors_log_saving {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ W Z K B : ℕ, (X : ℝ) ^ β ≤ W → 3 * X ≤ B → B ≤ 4 * X →
      Z ≤ B + 1 → ∀ δ : ℝ, 0 < δ →
      (∫ y : ℝ, clippedRoughError W Z K (primePartitionCount X) B δ y) ≤
        τ / (Real.log X) ^ 2 ∧
      ∀ P : Finset ℕ, P ⊆ Finset.Icc 1 B →
        (∫ y : ℝ, clippedCofactorError P W Z K (primePartitionCount X) B δ y) ≤
          τ / (Real.log X) ^ 2 := by
  filter_upwards [clipped_cutoff_cubic_log_saving hβ hτ, eventually_ge_atTop 1] with X hsave hX
  intro W Z K B hW hB hBX hZ δ hδ
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hWpos : 0 < W := by exact_mod_cast (Real.rpow_pos_of_pos hXp β).trans_le hW
  have hBpos : 1 ≤ B := by omega
  have hs := hsave W B hW hB hBX
  constructor
  · apply (clippedRoughError_integral_le hWpos K (primePartitionCount X) B hZ hδ).trans
    apply le_trans _ hs
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (harmonic_cast_one_le hBpos) (by decide : 2 ≤ 3)) (by positivity)
  · intro P hP
    exact (clippedCofactorError_integral_le P hWpos K (primePartitionCount X) B hZ hP hδ).trans hs

end Erdos421
