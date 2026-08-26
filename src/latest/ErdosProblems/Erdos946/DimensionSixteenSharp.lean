/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BinomialEulerProductSharp
import ErdosProblems.Erdos387.SieveInstantiation
import ErdosProblems.Erdos851.LocalEulerProducts

/-!
# A sharp dimension majorant for the sixteen-form sieve

For `p ≥ 272`, the local factor with density `16 / p` is bounded by
seventeen copies of the ordinary one-dimensional factor.  This deliberately
uses dimension `17`, rather than paying the very large uniform constant in a
dimension-exact comparison.  Combined with the explicit Mertens product
bounds, it gives the clean constant `3 ^ 17` needed by the quantitative
argument for Erdős 946.
-/

namespace Erdos946.DimensionSixteenSharp

open scoped BigOperators
open Erdos851 Erdos387

/-- Beyond `272`, one binomial local factor of density `16 / p` is bounded
by seventeen one-shift factors. -/
theorem binomial16_inverseLocalFactor_le_oneShift_pow_seventeen
    {p : ℕ} (hp : p.Prime) (hpLarge : 272 ≤ p) :
    (1 - binomialSieveNu 16 p)⁻¹ ≤
      (1 - oneShiftDensity p)⁻¹ ^ (17 : ℕ) := by
  let x : ℝ := (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h272 : (0 : ℝ) < 272 := by norm_num
  have hx : 0 ≤ x := inv_nonneg.mpr hpR.le
  have hxSmall : x ≤ (1 : ℝ) / 272 := by
    dsimp [x]
    have hpLargeR : (272 : ℝ) ≤ p := by exact_mod_cast hpLarge
    simpa only [one_div] using (inv_le_inv₀ hpR h272).2 hpLargeR
  have hxOne : x < 1 := by
    exact hxSmall.trans_lt (by norm_num)
  have hone : 0 < 1 - x := sub_pos.mpr hxOne
  have hpowExp : (1 - x) ^ (17 : ℕ) ≤ Real.exp (-(17 * x)) := by
    calc
      (1 - x) ^ (17 : ℕ) ≤ (Real.exp (-x)) ^ (17 : ℕ) :=
        pow_le_pow_left₀ hone.le (Real.one_sub_le_exp_neg x) 17
      _ = Real.exp (-(17 * x)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hadd : 1 + 17 * x ≤ Real.exp (17 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (17 * x)
  have hexpInv : Real.exp (-(17 * x)) ≤ (1 + 17 * x)⁻¹ := by
    rw [show -(17 * x) = -(17 * x) by rfl, Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hadd
  have hquad : 272 * x ^ 2 ≤ x := by
    have hmul := mul_le_mul_of_nonneg_left hxSmall hx
    norm_num at hmul ⊢
    nlinarith
  have hden : 0 < 1 + 17 * x := by positivity
  have hinvLinear : (1 + 17 * x)⁻¹ ≤ 1 - 16 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    nlinarith
  have hpow : (1 - x) ^ (17 : ℕ) ≤ 1 - 16 * x :=
    hpowExp.trans (hexpInv.trans hinvLinear)
  have hbin : 0 < 1 - 16 * x := by
    have : 16 * x < 1 := by
      calc
        16 * x ≤ 16 * ((1 : ℝ) / 272) := by gcongr
        _ < 1 := by norm_num
    linarith
  have hinv := (inv_le_inv₀ hbin (pow_pos hone 17)).2 hpow
  rw [binomialSieveNu_prime hp]
  change (1 - (16 : ℝ) / p)⁻¹ ≤
    (1 - (p : ℝ)⁻¹)⁻¹ ^ (17 : ℕ)
  simpa [x, oneShiftDensity, div_eq_mul_inv, inv_pow] using hinv

/-- The finite inverse Euler product for the density `16 / p` is bounded
by the seventeenth power of the ordinary inverse Mertens product. -/
theorem binomial16_inverseLocalEulerProduct_le_oneShift_pow_seventeen
    {z y : ℕ} (hz : 271 ≤ z) :
    inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) z y ≤
      inverseLocalEulerProduct oneShiftDensity z y ^ (17 : ℕ) := by
  simp only [inverseLocalEulerProduct]
  calc
    (∏ p ∈ Erdos851.sievePrimes z y, (1 - binomialSieveNu 16 p)⁻¹) ≤
        ∏ p ∈ Erdos851.sievePrimes z y,
          (1 - oneShiftDensity p)⁻¹ ^ (17 : ℕ) := by
      apply Finset.prod_le_prod
      · intro p hpMem
        have hp' := mem_sievePrimes.mp hpMem
        rw [binomialSieveNu_prime hp'.2.2]
        apply inv_nonneg.mpr
        rw [sub_nonneg, div_le_one (by exact_mod_cast hp'.2.2.pos)]
        exact_mod_cast (show 16 ≤ p by omega)
      · intro p hpMem
        have hp' := mem_sievePrimes.mp hpMem
        exact binomial16_inverseLocalFactor_le_oneShift_pow_seventeen
          hp'.2.2 (by omega)
    _ = (∏ p ∈ Erdos851.sievePrimes z y,
          (1 - oneShiftDensity p)⁻¹) ^ (17 : ℕ) := by
      rw [Finset.prod_pow]

/-- A constant-`3^17` dimension-17 bound, valid uniformly once the lower
endpoint is at least `272`. -/
theorem binomial16_dimension_seventeen
    {z y : ℕ} (hz : 272 ≤ z) (hzy : z ≤ y) :
    inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) z y ≤
      (3 : ℝ) ^ (17 : ℕ) *
        (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ (17 : ℕ) := by
  have hz3 : 3 ≤ z := by omega
  have hy3 : 3 ≤ y := hz3.trans hzy
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hPEPz : 0 < partial_euler_product z :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hquot : partial_euler_product y / partial_euler_product z ≤
      3 * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
    calc
      partial_euler_product y / partial_euler_product z ≤
          (3 * Real.log (y : ℝ)) / Real.log (z : ℝ) := by
        exact div_le_div₀ (by positivity)
          (Erdos387.BinomialEulerProductSharp.partialEulerProduct_le_three_mul_log hy3)
          hlogz
          (Erdos387.BinomialEulerProductSharp.log_le_partialEulerProduct z)
      _ = 3 * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by ring
  have hone : inverseLocalEulerProduct oneShiftDensity z y ≤
      3 * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
    rw [oneShift_inverseLocalEulerProduct_eq hzy]
    exact hquot
  have hone0 : 0 ≤ inverseLocalEulerProduct oneShiftDensity z y := by
    unfold inverseLocalEulerProduct
    apply Finset.prod_nonneg
    intro p hpMem
    exact inv_nonneg.mpr
      (oneShift_localFactor_pos (mem_sievePrimes.mp hpMem).2.2).le
  calc
    inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) z y ≤
        inverseLocalEulerProduct oneShiftDensity z y ^ (17 : ℕ) :=
      binomial16_inverseLocalEulerProduct_le_oneShift_pow_seventeen (by omega)
    _ ≤ (3 * (Real.log (y : ℝ) / Real.log (z : ℝ))) ^ (17 : ℕ) :=
      pow_le_pow_left₀ hone0 hone 17
    _ = (3 : ℝ) ^ (17 : ℕ) *
        (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ (17 : ℕ) := by
      rw [mul_pow]

end Erdos946.DimensionSixteenSharp
