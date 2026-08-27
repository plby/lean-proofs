/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceReserveGoodProbability
import ErdosProblems.Erdos207.ReserveReferencePowerBudgets
import ErdosProblems.Erdos207.PolynomialExponentialDecay

/-! # Uniform inverse-power reserve errors from explicit exponent gaps -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem reserve_internal_supply_power_lower
    (t u r p eta eta0 : ℝ≥0) (reserveExp b L gain : ℕ)
    (ht : 1 ≤ t) (hr : 1 / t ^ reserveExp ≤ r) (hp : 1 / t ^ b ≤ p)
    (heta : eta0 ≤ eta) (hu : t ^ L ≤ u) (hgap : 2 * reserveExp + 2 * b + gain ≤ L) :
    eta0 * t ^ gain ≤ r ^ 2 * p ^ 2 * eta * u := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpow : t ^ gain ≤ t ^ L / t ^ (2 * reserveExp + 2 * b) := by
    apply (le_div_iff₀ (pow_pos ht0 _)).mpr
    rw [← pow_add]
    exact pow_le_pow_right₀ ht (by omega)
  calc
    _ ≤ eta0 * (t ^ L / t ^ (2 * reserveExp + 2 * b)) := mul_le_mul_of_nonneg_left hpow zero_le
    _ = (1 / t ^ reserveExp) ^ 2 * (1 / t ^ b) ^ 2 * eta0 * t ^ L := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem sourceReserveFailureBound_le_exponential
    (N u t R : ℕ) (p eta r : ℝ≥0) (epsilon c : ℝ)
    (ht : 1 ≤ t) (hN : N ≤ t ^ R)
    (hinternal : c * t ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * u / 8)
    (hlink : c * t ≤ epsilon ^ 2 * ((r : ℝ) * (p : ℝ) ^ 3 * eta ^ 2 * u) / 32) :
    (sourceReserveFailureBound N u p eta r epsilon : ℝ) ≤
      7 * (t : ℝ) ^ (3 * R) * Real.exp (-c * t) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hNreal : (N : ℝ) ≤ (t : ℝ) ^ R := by exact_mod_cast hN
  have hpow1 : (1 : ℝ) ≤ (t : ℝ) ^ R := one_le_pow₀ ht1
  have hN1 : (N : ℝ) ≤ (t : ℝ) ^ (3 * R) := hNreal.trans (pow_le_pow_right₀ ht1 (by omega))
  have hN2 : (N : ℝ) ^ 2 ≤ (t : ℝ) ^ (3 * R) := by
    calc
      _ ≤ ((t : ℝ) ^ R) ^ 2 := pow_le_pow_left₀ (by positivity) hNreal _
      _ = (t : ℝ) ^ (R * 2) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ ht1 (by omega)
  have hN3 : (N : ℝ) ^ 3 ≤ (t : ℝ) ^ (3 * R) := by
    simpa only [← pow_mul, Nat.mul_comm R 3] using pow_le_pow_left₀ (by positivity) hNreal 3
  have hexpI : Real.exp (-(r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * u / 8) ≤ Real.exp (-c * t) := by
    apply Real.exp_le_exp.mpr
    linarith only [hinternal]
  have hexpL : Real.exp (-epsilon ^ 2 * ((r : ℝ) * (p : ℝ) ^ 3 * eta ^ 2 * u) / 32) ≤ Real.exp (-c * t) := by
    apply Real.exp_le_exp.mpr
    linarith only [hlink]
  simp only [sourceReserveFailureBound, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_ofNat, Real.coe_toNNReal _ (Real.exp_pos _).le]
  calc
    _ ≤ (t : ℝ) ^ (3 * R) * Real.exp (-c * t) + 6 * (t : ℝ) ^ (3 * R) * Real.exp (-c * t) := by
      apply add_le_add
      · exact mul_le_mul hN2 hexpI (Real.exp_pos _).le (by positivity)
      · exact mul_le_mul (by linarith only [hN1,hN2,hN3]) hexpL (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem eventually_sourceReserveFailureBound_le_power
    (reserveExp b e L R decay : ℕ) (eta0 epsilon0 error0 : ℝ≥0)
    (heta0 : 0 < eta0) (hepsilon0 : 0 < epsilon0) (herror0 : 0 < error0)
    (hI : 2 * reserveExp + 2 * b + 1 ≤ L) (hL : reserveExp + 3 * b + 2 * e + 1 ≤ L) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N u : ℕ) (p eta r epsilon : ℝ≥0),
      N ≤ t ^ R → t ^ L ≤ u → 1 / (t : ℝ≥0) ^ b ≤ p →
      1 / (t : ℝ≥0) ^ reserveExp ≤ r → eta0 ≤ eta →
      epsilon0 / (t : ℝ≥0) ^ e ≤ epsilon →
      sourceReserveFailureBound N u p eta r epsilon ≤ error0 / (t : ℝ≥0) ^ decay := by
  let c : ℝ := min ((eta0 : ℝ) / 8) ((epsilon0 : ℝ) ^ 2 * (eta0 : ℝ) ^ 2 / 32)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  obtain ⟨T,hT1,hT⟩ := eventually_polynomial_exp_neg_mul_lt 7 c error0 (3 * R + decay) hc (by exact_mod_cast herror0)
  refine ⟨T,hT1,fun t ht N u p eta r epsilon hN hu hp hr heta hepsilon ↦ ?_⟩
  have ht1 : 1 ≤ t := hT1.trans ht
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have huNN : (t : ℝ≥0) ^ L ≤ u := by exact_mod_cast hu
  have hinternal : eta0 * t ≤ r ^ 2 * p ^ 2 * eta * u := by
    simpa only [pow_one] using reserve_internal_supply_power_lower t u r p eta eta0 reserveExp b L 1
      htNN hr hp heta huNN hI
  have hlink := reserve_link_reference_power_lower (t : ℝ≥0) u r p eta eta0 reserveExp b L (2 * e + 1)
    htNN hr hp heta huNN (by omega)
  have hepslink : epsilon0 ^ 2 * eta0 ^ 2 * t ≤ epsilon ^ 2 * (r * p ^ 3 * eta ^ 2 * u) := by
    calc
      _ = (epsilon0 / (t : ℝ≥0) ^ e) ^ 2 * (eta0 ^ 2 * (t : ℝ≥0) ^ (2 * e + 1)) := by
        simp only [pow_add, pow_mul, pow_one, div_pow]
        field_simp
        ring
      _ ≤ _ := mul_le_mul (pow_le_pow_left' hepsilon 2) hlink zero_le zero_le
  have hiR : (eta0 : ℝ) * t ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * u := by exact_mod_cast hinternal
  have hlR : (epsilon0 : ℝ) ^ 2 * (eta0 : ℝ) ^ 2 * t ≤ (epsilon : ℝ) ^ 2 * ((r : ℝ) * (p : ℝ) ^ 3 * eta ^ 2 * u) := by
    exact_mod_cast hepslink
  have hiC := mul_le_mul_of_nonneg_right
    (min_le_left ((eta0 : ℝ) / 8) ((epsilon0 : ℝ) ^ 2 * (eta0 : ℝ) ^ 2 / 32))
    (show (0 : ℝ) ≤ t by positivity)
  have hlC := mul_le_mul_of_nonneg_right
    (min_le_right ((eta0 : ℝ) / 8) ((epsilon0 : ℝ) ^ 2 * (eta0 : ℝ) ^ 2 / 32))
    (show (0 : ℝ) ≤ t by positivity)
  have hb := sourceReserveFailureBound_le_exponential N u t R p eta r epsilon c ht1 hN
    (by dsimp only [c]; linarith only [hiC,hiR])
    (by dsimp only [c]; linarith only [hlC,hlR])
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast]
  apply hb.trans
  apply (le_div_iff₀ (by exact_mod_cast (pow_pos ht0 decay))).mpr
  have hsmall := (hT t ht).le
  rw [pow_add] at hsmall
  nlinarith only [hsmall]

end

end Erdos207
