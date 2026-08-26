import ErdosProblems.Erdos421.PrimeCofactorFullWindowEnergy
import ErdosProblems.Erdos421.LogWindowScales

/-! # Arbitrary logarithmic savings for the full smooth-window energy -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Filter Topology
open scoped SchwartzMap

theorem prime_cofactor_log_window_energy (φ : 𝓢(ℝ, ℂ)) {δ e A ε : ℝ}
    (hδ : 0 < δ) (he : 0 < e) (he' : e < 9 / 10) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℕ in atTop,
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-B) ∧
      ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ δ ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ ρ : ℝ, 1 ≤ σ → 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ →
      ρ ≤ (Real.log X) ^ (-B) →
      (∫ t : ℝ, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2 *
          ‖windowMultiplier φ (4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)) ρ t‖ ^ 2) ≤
        ε / (Real.log X) ^ A := by
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨C, hC, K, hK, henergy⟩ :=
    prime_cofactor_full_window_energy φ 5 hδ he he' hA hquarter
  let ℓ : ℝ := 2 * (A + twoFactorSampleExponent (primeFactorMaxMoment δ)) + 13
  let B : ℝ := (3 * ℓ + A + 1) / 2
  have hB : 0 < B := by dsimp only [B, ℓ]; positivity
  have hεtail : 0 < ε / (16 * K ^ 2) := by positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [henergy, log_power_le_half_eventually ℓ,
    short_window_below_log_scale (by linarith : 0 < 9 / 10 - e) B,
    constant_inverse_log_saving (2 * (C / (2 * Real.pi)) ^ 2) A hquarter,
    inverse_log_above_inverse_power (by norm_num : (0 : ℝ) < 1 / 5) hεtail A,
    eventually_ge_atTop (2 : ℕ)] with X hmain hcut hscale hlowabs htailabs hX
  refine ⟨hscale, ?_⟩
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ ρ hσ hρlo hρhi
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hRp : 0 < (X : ℝ) ^ (9 / 10 - e) := Real.rpow_pos_of_pos hXp _
  have hρp : 0 < ρ := (by positivity : 0 < 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)).trans_le hρlo
  have hUV : (Real.log X) ^ ℓ ≤ (X : ℝ) - 1 := by linarith
  have hb := hmain M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard
    σ ((Real.log X) ^ ℓ) ((X : ℝ) - 1) ρ hσ le_rfl hUV (by linarith) hρlo
  have hρpower : ρ ≤ (Real.log X) ^ (-(3 * ℓ + A + 1) / 2) := by
    convert hρhi using 1
    congr 1
    dsimp only [B]
    ring
  have hlowpower := logarithmic_window_low_power hL hρp.le hρpower
  have hlow : 2 * (C * ρ / (2 * Real.pi)) ^ 2 * ((Real.log X) ^ ℓ) ^ 3 ≤
      (ε / 4) / (Real.log X) ^ A := by
    apply le_trans _ hlowabs
    have hm := mul_le_mul_of_nonneg_left hlowpower
      (by positivity : 0 ≤ 2 * (C / (2 * Real.pi)) ^ 2)
    convert hm using 1
    ring
  have hRX : (X : ℝ) ^ (9 / 10 - e) ≤ (X : ℝ) ^ (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have htail := window_sixth_decay_tail_power hXp hRp.le hRX
    (by linarith : (X : ℝ) / 2 ≤ (X : ℝ) - 1) hK.le
  have ht : 2 * ((2 * K * (((X : ℝ) ^ (9 / 10 - e)) / 2) ^ 6) ^ 2 /
      (((X : ℝ) - 1) ^ 5) ^ 2 / ((X : ℝ) - 1)) ≤ (ε / 4) / (Real.log X) ^ A := by
    have hm := mul_le_mul_of_nonneg_left htailabs (by positivity : 0 ≤ 4 * K ^ 2)
    have heq : 4 * K ^ 2 * ((ε / (16 * K ^ 2)) / (Real.log X) ^ A) =
        (ε / 4) / (Real.log X) ^ A := by
      have hKn : K ≠ 0 := hK.ne'
      field_simp
      ring
    rw [heq] at hm
    nlinarith only [htail, hm]
  have heq : 2 * ((ε / 4) / (Real.log X) ^ A) +
      (ε / 4) / (Real.log X) ^ A + (ε / 4) / (Real.log X) ^ A = ε / (Real.log X) ^ A := by ring
  linarith only [hb, hlow, ht, heq]

end Erdos421
