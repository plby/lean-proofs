import ErdosProblems.Erdos587.FourierDecay
import ErdosProblems.Erdos587.WideScales

/-!
# Rounded cutoffs for fixed smooth weights

The base cutoff is the ceiling of the reciprocal physical scale. The
enlarged cutoff is its unrounded scale times `T^(1/100)`, rounded down.
-/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma normalized_frequency_cutoffs {r Y : ℝ} (hr : 1 ≤ r) (hY : 4 ≤ Y) :
    let M := ⌈r⌉₊
    let N := ⌊r * Y⌋₊
    0 < M ∧ M ≤ N ∧ r ≤ (M : ℝ) ∧ (N : ℝ) ≤ r * Y ∧
      1 ≤ r⁻¹ * M ∧ r⁻¹ * M ≤ 2 ∧ Y / 2 ≤ r⁻¹ * N := by
  dsimp only
  have hrpos : 0 < r := by linarith
  have hceil : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
  have hceilhi : (⌈r⌉₊ : ℝ) ≤ 2 * r := by
    have hh := Nat.ceil_lt_add_one hrpos.le
    linarith
  have hprod : 2 ≤ r * Y := by nlinarith
  have hhalf := half_le_nat_floor hprod
  have hMpos : 0 < ⌈r⌉₊ := by exact_mod_cast hrpos.trans_le hceil
  have hMN : ⌈r⌉₊ ≤ ⌊r * Y⌋₊ := by
    have hh : (⌈r⌉₊ : ℝ) ≤ (⌊r * Y⌋₊ : ℝ) := by nlinarith
    exact_mod_cast hh
  refine ⟨hMpos, hMN, hceil, Nat.floor_le (by linarith), ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hceil (inv_pos.mpr hrpos).le
    simpa only [inv_mul_cancel₀ hrpos.ne'] using hh
  · have hh := mul_le_mul_of_nonneg_left hceilhi (inv_pos.mpr hrpos).le
    calc
      _ ≤ r⁻¹ * (2 * r) := hh
      _ = 2 := by field_simp
  · have hh := mul_le_mul_of_nonneg_left hhalf (inv_pos.mpr hrpos).le
    calc
      Y / 2 = r⁻¹ * (r * Y / 2) := by field_simp
      _ ≤ _ := hh

theorem eventually_scaled_schwartz_power_tail (g : 𝓢(ℝ, ℂ)) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 1 ≤ r →
      let N := ⌊r * T ^ (1 / 100 : ℝ)⌋₊
      (∑' n : ℕ, if N < n + 1 then
        ‖((r⁻¹ : ℝ) : ℂ) * g (r⁻¹ * (n + 1))‖ else 0) ≤ 1 / T ^ 2 := by
  obtain ⟨C, hC, htail⟩ := exists_scaled_schwartz_positive_tail_bound g 300
  filter_upwards [eventually_ge_atTop (max 1 (C * 2 ^ 300)),
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 100 by norm_num)).eventually_ge_atTop 4]
    with T hT hpower
  intro r hr
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hCsize : C * 2 ^ 300 ≤ T := (le_max_right _ _).trans hT
  have hrpos : 0 < r := by linarith
  obtain ⟨hM, hMN, hrM, hNhi, hscale₀, hscale₁, hscaleN⟩ :=
    normalized_frequency_cutoffs hr hpower
  let N := ⌊r * T ^ (1 / 100 : ℝ)⌋₊
  have hN : 0 < N := hM.trans_le hMN
  have htail' := (htail r⁻¹ ⌈r⌉₊ N (inv_pos.mpr hrpos) hM hN hscale₀ hscale₁).2
  have hden : 0 < r⁻¹ * (N : ℝ) := mul_pos (inv_pos.mpr hrpos) (by exact_mod_cast hN)
  have hp : T ^ 3 / 2 ^ 300 ≤ (r⁻¹ * (N : ℝ)) ^ 300 := by
    calc
      _ = (T ^ (1 / 100 : ℝ) / 2) ^ 300 := by
        rw [div_pow, ← Real.rpow_mul_natCast hTpos.le]
        norm_num
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hscaleN 300
  apply htail'.trans
  calc
    _ ≤ C / (T ^ 3 / 2 ^ 300) :=
      div_le_div_of_nonneg_left hC.le (by positivity) hp
    _ = (C * 2 ^ 300) / T ^ 3 := by rw [div_div_eq_mul_div]
    _ ≤ T / T ^ 3 := div_le_div_of_nonneg_right hCsize (by positivity)
    _ = 1 / T ^ 2 := by field_simp

end Erdos587
