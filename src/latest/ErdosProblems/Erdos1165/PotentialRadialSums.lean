/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialFourierIntegral

/-!
# Elementary summation estimates for the radial potential asymptotic

This file isolates the one-variable real estimates used when the local CLT
is summed over time.  The constants are deliberately generous.  The useful
scaling is

`rho^3 * sum_{n >= rho^2} n^-3 = O(rho^-1)`.
-/

open Filter Real
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialRadialSums

/-- A fourth-order polynomial majorant for a negative exponential. -/
theorem exp_neg_le_twentyFour_div_pow_four {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 24 / x ^ 4 := by
  have hfourth : x ^ 4 / 24 ≤ Real.exp x := by
    have h := Real.pow_div_factorial_le_exp x hx.le 4
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos x) (pow_pos hx 4)).2
  nlinarith

/-- Uniform reciprocal-cube tail. -/
theorem tsum_one_div_cube_shift_le {M : ℕ} (hM : 0 < M) :
    ∑' n : ℕ, 1 / (((n + M : ℕ) : ℝ) ^ 3) ≤
      2 / (M : ℝ) ^ 2 := by
  have hf : Summable (fun n : ℕ ↦ 1 / (((n + M : ℕ) : ℝ) ^ 3)) := by
    exact (summable_nat_add_iff M).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have hcomp := PotentialFourierIntegral.hasSum_inverse_nat_mul_succ_shift hM
  have hg := hcomp.summable.mul_left (2 / (M : ℝ))
  calc
    ∑' n : ℕ, 1 / (((n + M : ℕ) : ℝ) ^ 3) ≤
        ∑' n : ℕ, (2 / (M : ℝ)) *
          (1 / (((n + M : ℕ) : ℝ) * (n + M + 1))) := by
      apply Summable.tsum_le_tsum _ hf hg
      intro n
      have hMR : (0 : ℝ) < M := by exact_mod_cast hM
      have hnMR : (0 : ℝ) < n + M := by positivity
      have hleM : (M : ℝ) ≤ n + M := by
        exact_mod_cast (by omega : M ≤ n + M)
      have hsucc : (n + M + 1 : ℝ) ≤ 2 * (n + M) := by
        have hone : (1 : ℝ) ≤ n + M := by exact_mod_cast (by omega : 1 ≤ n + M)
        norm_num only [Nat.cast_add, Nat.cast_one]
        linarith
      rw [div_eq_mul_inv]
      field_simp
      have hmul := mul_le_mul hleM hsucc (by positivity : (0 : ℝ) ≤ n + M + 1)
        (by positivity : (0 : ℝ) ≤ n + M)
      norm_num only [Nat.cast_add, Nat.cast_one] at hmul ⊢
      nlinarith
    _ = (2 / (M : ℝ)) * (1 / (M : ℝ)) :=
      (hcomp.mul_left _).tsum_eq
    _ = 2 / (M : ℝ) ^ 2 := by ring

/-- The Gaussian reciprocal-square weight used after the local CLT. -/
noncomputable def squareGaussianWeight (Q n : ℕ) : ℝ :=
  Real.exp (-(Q : ℝ) / (2 * (n + 1))) / (n + 1 : ℝ) ^ 2

/-- The Gaussian reciprocal-cube weight used after the local CLT. -/
noncomputable def cubeGaussianWeight (Q n : ℕ) : ℝ :=
  Real.exp (-(Q : ℝ) / (2 * (n + 1))) / (n + 1 : ℝ) ^ 3

theorem summable_squareGaussianWeight (Q : ℕ) :
    Summable (squareGaussianWeight Q) := by
  have hbase : Summable (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply Summable.of_nonneg_of_le
    (fun n ↦ by unfold squareGaussianWeight; positivity)
    (fun n ↦ ?_)
    hbase
  unfold squareGaussianWeight
  have hexp : Real.exp (-(Q : ℝ) / (2 * (n + 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg Q))
      (mul_nonneg (by norm_num) (by positivity))
  exact div_le_div_of_nonneg_right hexp (by positivity)

theorem summable_cubeGaussianWeight (Q : ℕ) :
    Summable (cubeGaussianWeight Q) := by
  have hbase : Summable (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ) ^ 3) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply Summable.of_nonneg_of_le
    (fun n ↦ by unfold cubeGaussianWeight; positivity)
    (fun n ↦ ?_)
    hbase
  unfold cubeGaussianWeight
  have hexp : Real.exp (-(Q : ℝ) / (2 * (n + 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg Q))
      (mul_nonneg (by norm_num) (by positivity))
  exact div_le_div_of_nonneg_right hexp (by positivity)

private theorem sum_square_early_le {Q : ℕ} (hQ : 0 < Q) :
    ∑ n ∈ Finset.range Q, squareGaussianWeight Q n ≤ 384 / (Q : ℝ) := by
  calc
    ∑ n ∈ Finset.range Q, squareGaussianWeight Q n ≤
        ∑ n ∈ Finset.range Q, 384 * (n + 1 : ℝ) ^ 2 / (Q : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hx : (0 : ℝ) < (Q : ℝ) / (2 * (n + 1)) := by positivity
      have he := exp_neg_le_twentyFour_div_pow_four hx
      unfold squareGaussianWeight
      calc
        Real.exp (-(Q : ℝ) / (2 * (n + 1))) / (n + 1 : ℝ) ^ 2 ≤
            (24 / (((Q : ℝ) / (2 * (n + 1))) ^ 4)) /
              (n + 1 : ℝ) ^ 2 := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                simpa [neg_div] using he
        _ = 384 * (n + 1 : ℝ) ^ 2 / (Q : ℝ) ^ 4 := by
          field_simp
          ring
    _ ≤ ∑ _n ∈ Finset.range Q, 384 * (Q : ℝ) ^ 2 / (Q : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlt := Finset.mem_range.mp hn
      have hnQ : (n + 1 : ℕ) ≤ Q := by omega
      have hnQR : (n + 1 : ℝ) ≤ Q := by exact_mod_cast hnQ
      gcongr
    _ = 384 / (Q : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hQ0 : (Q : ℝ) ≠ 0 := by positivity
      field_simp

private theorem sum_cube_early_le {Q : ℕ} (hQ : 0 < Q) :
    ∑ n ∈ Finset.range Q, cubeGaussianWeight Q n ≤ 384 / (Q : ℝ) ^ 2 := by
  calc
    ∑ n ∈ Finset.range Q, cubeGaussianWeight Q n ≤
        ∑ n ∈ Finset.range Q, 384 * (n + 1 : ℝ) / (Q : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hx : (0 : ℝ) < (Q : ℝ) / (2 * (n + 1)) := by positivity
      have he := exp_neg_le_twentyFour_div_pow_four hx
      unfold cubeGaussianWeight
      calc
        Real.exp (-(Q : ℝ) / (2 * (n + 1))) / (n + 1 : ℝ) ^ 3 ≤
            (24 / (((Q : ℝ) / (2 * (n + 1))) ^ 4)) /
              (n + 1 : ℝ) ^ 3 := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                simpa [neg_div] using he
        _ = 384 * (n + 1 : ℝ) / (Q : ℝ) ^ 4 := by
          field_simp
          ring
    _ ≤ ∑ _n ∈ Finset.range Q, 384 * (Q : ℝ) / (Q : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlt := Finset.mem_range.mp hn
      have hnQ : (n + 1 : ℕ) ≤ Q := by omega
      have hnQR : (n + 1 : ℝ) ≤ Q := by exact_mod_cast hnQ
      gcongr
    _ = 384 / (Q : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hQ0 : (Q : ℝ) ≠ 0 := by positivity
      field_simp

/-- Summed Gaussian square weight, with its scale-sharp `Q⁻¹` bound. -/
theorem tsum_squareGaussianWeight_le {Q : ℕ} (hQ : 0 < Q) :
    ∑' n : ℕ, squareGaussianWeight Q n ≤ 400 / (Q : ℝ) := by
  have hs := summable_squareGaussianWeight Q
  rw [← hs.sum_add_tsum_nat_add Q]
  have hearly := sum_square_early_le hQ
  have htail : ∑' n : ℕ, squareGaussianWeight Q (n + Q) ≤ 1 / (Q : ℝ) := by
    have hcomp := PotentialFourierIntegral.hasSum_inverse_nat_mul_succ_shift hQ
    calc
      ∑' n : ℕ, squareGaussianWeight Q (n + Q) ≤
          ∑' n : ℕ, 1 / (((n + Q : ℕ) : ℝ) * (n + Q + 1)) := by
        apply Summable.tsum_le_tsum _ ((summable_nat_add_iff Q).mpr hs) hcomp.summable
        intro n
        unfold squareGaussianWeight
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hexp : Real.exp (-(Q : ℝ) / (2 * (n + Q + 1))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg Q))
            (mul_nonneg (by norm_num) (by positivity))
        calc
          Real.exp (-(Q : ℝ) / (2 * (n + Q + 1))) / (n + Q + 1 : ℝ) ^ 2 ≤
              1 / (n + Q + 1 : ℝ) ^ 2 := by gcongr
          _ ≤ 1 / ((n + Q : ℝ) * (n + Q + 1)) := by
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith
      _ = 1 / (Q : ℝ) := hcomp.tsum_eq
  calc
    (∑ n ∈ Finset.range Q, squareGaussianWeight Q n) +
        ∑' n : ℕ, squareGaussianWeight Q (n + Q) ≤
      384 / (Q : ℝ) + 1 / (Q : ℝ) := add_le_add hearly htail
    _ ≤ 400 / (Q : ℝ) := by
      have hQ0 : (Q : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num

/-- Summed Gaussian cube weight, with its scale-sharp `Q⁻²` bound. -/
theorem tsum_cubeGaussianWeight_le {Q : ℕ} (hQ : 0 < Q) :
    ∑' n : ℕ, cubeGaussianWeight Q n ≤ 400 / (Q : ℝ) ^ 2 := by
  have hs := summable_cubeGaussianWeight Q
  rw [← hs.sum_add_tsum_nat_add Q]
  have hearly := sum_cube_early_le hQ
  have htail : ∑' n : ℕ, cubeGaussianWeight Q (n + Q) ≤
      2 / ((Q + 1 : ℕ) : ℝ) ^ 2 := by
    have hc := tsum_one_div_cube_shift_le (show 0 < Q + 1 by omega)
    have hcube : Summable (fun n : ℕ ↦
        1 / (((n + (Q + 1) : ℕ) : ℝ) ^ 3)) := by
      have h := (summable_nat_add_iff (Q + 1)).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ)))
      simpa only using h
    calc
      ∑' n : ℕ, cubeGaussianWeight Q (n + Q) ≤
          ∑' n : ℕ, 1 / (((n + (Q + 1) : ℕ) : ℝ) ^ 3) := by
        apply Summable.tsum_le_tsum _ ((summable_nat_add_iff Q).mpr hs) hcube
        intro n
        unfold cubeGaussianWeight
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hexp : Real.exp (-(Q : ℝ) / (2 * (n + Q + 1))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg Q))
            (mul_nonneg (by norm_num) (by positivity))
        have hmain := div_le_div_of_nonneg_right hexp
          (pow_nonneg (by positivity : (0 : ℝ) ≤ n + Q + 1) 3)
        convert hmain using 1 <;> ring
      _ ≤ 2 / ((Q + 1 : ℕ) : ℝ) ^ 2 := hc
  have htail' : ∑' n : ℕ, cubeGaussianWeight Q (n + Q) ≤
      2 / (Q : ℝ) ^ 2 := by
    refine htail.trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
    norm_num
  calc
    (∑ n ∈ Finset.range Q, cubeGaussianWeight Q n) +
        ∑' n : ℕ, cubeGaussianWeight Q (n + Q) ≤
      384 / (Q : ℝ) ^ 2 + 2 / (Q : ℝ) ^ 2 := add_le_add hearly htail'
    _ ≤ 400 / (Q : ℝ) ^ 2 := by
      have hQ0 : (Q : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num

end PotentialRadialSums
end Erdos1165
