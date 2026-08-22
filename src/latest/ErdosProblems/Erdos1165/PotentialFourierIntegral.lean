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

import ErdosProblems.Erdos1165.PotentialKernel
import ErdosProblems.Erdos1165.BinomialGaussian
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-!
# The sharp logarithmic planar potential estimate

This file upgrades the pointwise convergence result in
`PotentialConvergence.lean` to the uniform logarithmic estimate needed in
planar potential theory.  We use the diagonal Fourier coordinates of the
walk.  In these coordinates the two Fourier coefficients are centered
binomial masses, so all estimates below are exact finite coefficient
estimates.

The main theorem is `diagonalPotential_log_asymptotic_bound`: for
`R = max d e > 0`,

`|diagonalPotential d e - (2 / π) * log R| ≤ 100`.

In particular this proves, with an explicit uniform error, the classical
asymptotic `a(x) = (2/π) log |x| + O(1)` (using the max norm in diagonal
coordinates; changing between lattice norms only changes the bounded error).
-/

open Filter Real
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialFourierIntegral

open BinomialGaussian PotentialKernel StirlingLocalCLT

/-! ## Fourier coefficients and the potential series -/

/-- Product of the two centered-binomial Fourier coefficients. -/
noncomputable def fourierProductMass (n d e : ℕ) : ℝ :=
  evenSymmetricMass n d * evenSymmetricMass n e

/-- Loss of the coefficient at diagonal frequency `(d,e)` from the constant
coefficient. -/
noncomputable def fourierProductLoss (d e n : ℕ) : ℝ :=
  fourierProductMass n 0 0 - fourierProductMass n d e

lemma fourierProductMass_center (n : ℕ) :
    fourierProductMass n 0 0 = planarReturnProbability n := by
  have hpow : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  unfold fourierProductMass evenSymmetricMass symBinomialMass planarReturnProbability
  rw [Nat.centralBinom_eq_two_mul_choose, hpow]
  rw [div_mul_div_comm]
  congr 1
  · norm_num
    ring
  · rw [← mul_pow]
    norm_num

theorem fourierProductLoss_nonneg (d e n : ℕ) :
    0 ≤ fourierProductLoss d e n := by
  unfold fourierProductLoss fourierProductMass
  have hd := evenSymmetricMass_le_center n d
  have he := evenSymmetricMass_le_center n e
  have h0d : 0 ≤ evenSymmetricMass n 0 := by
    unfold evenSymmetricMass symBinomialMass
    positivity
  have hde0 : 0 ≤ evenSymmetricMass n d := by
    unfold evenSymmetricMass symBinomialMass
    positivity
  nlinarith

/-! ## A global quadratic loss estimate -/

/-- The cubic moderate-deviation remainder is bounded by a quadratic
quantity on its stated window.  The deliberately generous constant makes the
bound uniform down to `n = 1`. -/
theorem center_sub_shift_quadratic {n d : ℕ} (hn : 0 < n) :
    evenSymmetricMass n 0 - evenSymmetricMass n d ≤
      (10 : ℝ) * (d + 1 : ℝ) ^ 2 / n * evenSymmetricMass n 0 := by
  by_cases hd : d < n
  · by_cases hmoderate : 2 * d ≤ n
    · have hraw := (evenSymmetricMass_center_sub_le hn hd hmoderate).2
      let E : ℝ := 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
        (1 : ℝ) / (6 * (n - d)) + (1 : ℝ) / (6 * n)
      have hnR : (0 : ℝ) < n := by positivity
      have hndR : (0 : ℝ) < n - d := by
        exact sub_pos.mpr (by exact_mod_cast hd)
      have hhalf : (n : ℝ) / 2 ≤ n - d := by
        have hm : (2 : ℝ) * d ≤ n := by exact_mod_cast hmoderate
        linarith
      have hinvSub : (1 : ℝ) / (n - d) ≤ 2 / n := by
        rw [div_le_div_iff₀ hndR hnR]
        nlinarith
      have hrel : relativeDeviation n d = (d : ℝ) / n := rfl
      have hrel_nonneg : 0 ≤ relativeDeviation n d := by
        rw [hrel]
        positivity
      have hdhalf : (d : ℝ) ≤ n / 2 := by
        have hm : (2 : ℝ) * d ≤ n := by exact_mod_cast hmoderate
        linarith
      have hcube : 8 * (n : ℝ) * |relativeDeviation n d| ^ 3 ≤
          4 * (d : ℝ) ^ 2 / n := by
        rw [abs_of_nonneg hrel_nonneg, hrel]
        field_simp
        nlinarith [sq_nonneg (d : ℝ)]
      have hsquare : relativeDeviation n d ^ 2 ≤ (d : ℝ) ^ 2 / n := by
        rw [hrel]
        field_simp
        have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg (d : ℝ)]
      have hsub : (1 : ℝ) / (6 * ((n : ℝ) - d)) ≤ 1 / (3 * n) := by
        have h := mul_le_mul_of_nonneg_left hinvSub (by norm_num : (0 : ℝ) ≤ 1 / 6)
        calc
          (1 : ℝ) / (6 * ((n : ℝ) - d)) = (1 / 6) * (1 / ((n : ℝ) - d)) := by
            field_simp [ne_of_gt hndR]
          _ ≤ (1 / 6) * (2 / n) := h
          _ = 1 / (3 * n) := by
            field_simp [ne_of_gt hnR]
            norm_num
      have hcoeff : (d : ℝ) ^ 2 / n + E ≤
          10 * (d + 1 : ℝ) ^ 2 / n := by
        dsimp [E]
        calc
          (d : ℝ) ^ 2 / n +
              (8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
                1 / (6 * ((n : ℝ) - d)) + 1 / (6 * n)) ≤
              (d : ℝ) ^ 2 / n +
                (4 * (d : ℝ) ^ 2 / n + (d : ℝ) ^ 2 / n +
                  1 / (3 * n) + 1 / (6 * n)) := by gcongr
          _ ≤ 10 * (d + 1 : ℝ) ^ 2 / n := by
            field_simp
            nlinarith [sq_nonneg (d : ℝ)]
      exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff
        (evenSymmetricMass_pos (n := n) (d := 0) (by omega)).le)
    · have hloss : evenSymmetricMass n 0 - evenSymmetricMass n d ≤
          evenSymmetricMass n 0 := by
        have hm0 : 0 ≤ evenSymmetricMass n d := by
          unfold evenSymmetricMass symBinomialMass
          positivity
        linarith
      have hcoef : (1 : ℝ) ≤ 10 * (d + 1 : ℝ) ^ 2 / n := by
        have hnd : n < 2 * d := lt_of_not_ge hmoderate
        have hnR : (0 : ℝ) < n := by positivity
        rw [le_div_iff₀ hnR]
        have hndR : (n : ℝ) < 2 * d := by exact_mod_cast hnd
        nlinarith [sq_nonneg (d : ℝ)]
      exact hloss.trans (by
        nth_rewrite 1 [← one_mul (evenSymmetricMass n 0)]
        gcongr
        exact (evenSymmetricMass_pos (n := n) (d := 0) (by omega)).le)
  · have hloss : evenSymmetricMass n 0 - evenSymmetricMass n d ≤
        evenSymmetricMass n 0 := by
      have hm0 : 0 ≤ evenSymmetricMass n d := by
        unfold evenSymmetricMass symBinomialMass
        positivity
      linarith
    have hdn : n ≤ d := Nat.le_of_not_gt hd
    have hcoef : (1 : ℝ) ≤ 10 * (d + 1 : ℝ) ^ 2 / n := by
      have hnR : (0 : ℝ) < n := by positivity
      rw [le_div_iff₀ hnR]
      have hdnR : (n : ℝ) ≤ d := by exact_mod_cast hdn
      nlinarith [sq_nonneg (d : ℝ)]
    exact hloss.trans (by
      nth_rewrite 1 [← one_mul (evenSymmetricMass n 0)]
      gcongr
      exact (evenSymmetricMass_pos (n := n) (d := 0) (by omega)).le)

/-- The product Fourier coefficient has a quadratic, summable loss envelope,
uniformly in the displacement. -/
theorem fourierProductLoss_quadratic_le {d e n : ℕ} (hn : 0 < n) :
    fourierProductLoss d e n ≤
      10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) /
        ((n : ℝ) * (n + 1)) := by
  let c := evenSymmetricMass n 0
  let a := evenSymmetricMass n d
  let b := evenSymmetricMass n e
  have hca := center_sub_shift_quadratic (d := d) hn
  have hcb := center_sub_shift_quadratic (d := e) hn
  have ha0 : 0 ≤ a := by
    dsimp [a, evenSymmetricMass, symBinomialMass]
    positivity
  have hac : a ≤ c := evenSymmetricMass_le_center n d
  have hbc : b ≤ c := evenSymmetricMass_le_center n e
  have hc0 : 0 ≤ c := (evenSymmetricMass_pos (n := n) (d := 0) (by omega)).le
  have hreturn := planarReturnProbability_upper_bound n
  rw [← fourierProductMass_center] at hreturn
  change c * c ≤ 1 / (n + 1 : ℝ) at hreturn
  have hdecomp : fourierProductLoss d e n = (c - a) * c + a * (c - b) := by
    dsimp [fourierProductLoss, fourierProductMass, c, a, b]
    ring
  rw [hdecomp]
  calc
    (c - a) * c + a * (c - b) ≤
        (10 * (d + 1 : ℝ) ^ 2 / n * c) * c +
          c * (10 * (e + 1 : ℝ) ^ 2 / n * c) := by
      gcongr
    _ = (10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) / n) * (c * c) := by
      ring
    _ ≤ (10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) / n) *
        (1 / (n + 1 : ℝ)) := by
      gcongr
    _ = 10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) /
        ((n : ℝ) * (n + 1)) := by
      field_simp

/-! ## Convergence and a uniform tail -/

lemma summable_inverse_nat_mul_succ :
    Summable (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) * (n + 1))) := by
  have hsquare : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hsquare
  by_cases hn : n = 0
  · subst n
    simp
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * (n + 1))
        (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2
    nlinarith

/-- Exact telescoping value of the reciprocal-quadratic tail. -/
theorem hasSum_inverse_nat_mul_succ_shift {M : ℕ} (hM : 0 < M) :
    HasSum (fun n : ℕ ↦ (1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1))) (1 / (M : ℝ)) := by
  let f : ℕ → ℝ := fun n ↦ (1 : ℝ) / ((n + M : ℕ) : ℝ)
  have hterm (n : ℕ) :
      (1 : ℝ) / (((n + M : ℕ) : ℝ) * (n + M + 1)) = f n - f (n + 1) := by
    dsimp [f]
    push_cast
    field_simp
    ring
  have hsum : Summable (fun n : ℕ ↦ (1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff M).mpr summable_inverse_nat_mul_succ
  have hnorm : Summable (fun n : ℕ ↦ ‖(1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1))‖) := by
    apply hsum.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).2
  have hf_zero : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ by
        dsimp [f]
        positivity)
      (Filter.Eventually.of_forall fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show n + 1 ≤ n + M by omega)
  have hpartial : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, (1 : ℝ) /
          (((i + M : ℕ) : ℝ) * (i + M + 1)) = f 0 - f n := by
    intro n
    simp_rw [hterm]
    exact Finset.sum_range_sub' f n
  simp_rw [hpartial]
  simpa [f] using (tendsto_const_nhds.sub hf_zero)

theorem summable_fourierProductLoss (d e : ℕ) :
    Summable (fourierProductLoss d e) := by
  let C : ℝ := 10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2)
  apply (summable_nat_add_iff 1).mp
  have henv : Summable (fun n : ℕ ↦ C *
      ((1 : ℝ) / (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1)))) := by
    have hbase := (summable_nat_add_iff 1).mpr summable_inverse_nat_mul_succ
    exact (hbase.mul_left C).congr fun n ↦ by
      push_cast
      ring
  apply Summable.of_nonneg_of_le
    (fun n ↦ fourierProductLoss_nonneg d e (n + 1)) (fun n ↦ ?_) henv
  have h := fourierProductLoss_quadratic_le (d := d) (e := e)
    (show 0 < n + 1 by omega)
  dsimp [C]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Explicit uniform tail estimate. -/
theorem tsum_fourierProductLoss_shift_le {d e M : ℕ} (hM : 0 < M) :
    ∑' n : ℕ, fourierProductLoss d e (n + M) ≤
      10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) / M := by
  let C : ℝ := 10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2)
  have hf : Summable (fun n : ℕ ↦ fourierProductLoss d e (n + M)) :=
    (summable_nat_add_iff M).mpr (summable_fourierProductLoss d e)
  have hg : Summable (fun n : ℕ ↦ C * ((1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1)))) :=
    (hasSum_inverse_nat_mul_succ_shift hM).summable.mul_left C
  calc
    ∑' n : ℕ, fourierProductLoss d e (n + M) ≤
        ∑' n : ℕ, C * ((1 : ℝ) /
          (((n + M : ℕ) : ℝ) * (n + M + 1))) := by
      apply Summable.tsum_le_tsum _ hf hg
      intro n
      have h := fourierProductLoss_quadratic_le (d := d) (e := e)
        (show 0 < n + M by omega)
      dsimp [C]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    _ = C * (1 / (M : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((hasSum_inverse_nat_mul_succ_shift hM).mul_left C).tsum_eq
    _ = 10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) / M := by
      dsimp [C]
      ring

/-- The infinite potential in diagonal Fourier coordinates. -/
noncomputable def fourierPotential (d e : ℕ) : ℝ :=
  ∑' n : ℕ, fourierProductLoss d e n

theorem fourierPotential_nonneg (d e : ℕ) : 0 ≤ fourierPotential d e := by
  exact tsum_nonneg (fourierProductLoss_nonneg d e)

/-! ## Exponential decay of off-centre Fourier coefficients -/

/-- Exact adjacent ratio identity for the centered binomial coefficients. -/
lemma evenSymmetricMass_succ_mul {n d : ℕ} (hd : d < n) :
    evenSymmetricMass n (d + 1) * (n + d + 1 : ℝ) =
      evenSymmetricMass n d * (n - d : ℝ) := by
  have hnat := Nat.choose_succ_right_eq (2 * n) (n + d)
  have hnat' : (2 * n).choose (n + d + 1) * (n + d + 1) =
      (2 * n).choose (n + d) * (n - d) := by
    rw [show 2 * n - (n + d) = n - d by omega] at hnat
    simpa [Nat.add_assoc] using hnat
  have hreal : ((2 * n).choose (n + d + 1) : ℝ) * (n + d + 1 : ℝ) =
      ((2 * n).choose (n + d) : ℝ) * (n - d : ℕ) := by
    exact_mod_cast hnat'
  unfold evenSymmetricMass symBinomialMass
  field_simp
  simpa [Nat.cast_sub hd.le, Nat.add_assoc] using hreal

/-- A centered binomial Fourier coefficient has a global Gaussian upper
bound.  This elementary form follows only from the exact adjacent ratio and
`1-t ≤ exp(-t)`. -/
theorem evenSymmetricMass_le_center_mul_exp {n d : ℕ}
    (hn : 0 < n) (hd : d ≤ n) :
    evenSymmetricMass n d ≤ evenSymmetricMass n 0 *
      Real.exp (-((d : ℝ) ^ 2) / (2 * n)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hdlt : d < n := by omega
      have hdl : d ≤ n := hdlt.le
      have ih' := ih hdl
      have hrec := evenSymmetricMass_succ_mul (n := n) hdlt
      have hden : (0 : ℝ) < n + d + 1 := by positivity
      have hmass : evenSymmetricMass n (d + 1) =
          evenSymmetricMass n d * ((n - d : ℝ) / (n + d + 1)) := by
        field_simp [hden.ne']
        exact hrec
      have hratio_nonneg : (0 : ℝ) ≤ (n - d : ℝ) / (n + d + 1) := by
        exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hdl)) hden.le
      have hden_le : (n + d + 1 : ℝ) ≤ 2 * n := by
        have hnat : n + d + 1 ≤ 2 * n := by omega
        exact_mod_cast hnat
      have hratio : (n - d : ℝ) / (n + d + 1) ≤
          Real.exp (-((2 * d + 1 : ℕ) : ℝ) / (2 * n)) := by
        calc
          (n - d : ℝ) / (n + d + 1) =
              1 - ((2 * d + 1 : ℕ) : ℝ) / (n + d + 1) := by
            norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
            field_simp
            ring
          _ ≤ Real.exp (-(((2 * d + 1 : ℕ) : ℝ) / (n + d + 1))) :=
            Real.one_sub_le_exp_neg _
          _ ≤ Real.exp (-((2 * d + 1 : ℕ) : ℝ) / (2 * n)) := by
            apply Real.exp_le_exp.mpr
            rw [show -(((2 * d + 1 : ℕ) : ℝ)) / (2 * n) =
              -((((2 * d + 1 : ℕ) : ℝ) / (2 * n))) by ring]
            rw [neg_le_neg_iff]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_le
      rw [hmass]
      calc
        evenSymmetricMass n d * ((n - d : ℝ) / (n + d + 1)) ≤
            (evenSymmetricMass n 0 * Real.exp (-((d : ℝ) ^ 2) / (2 * n))) *
              Real.exp (-((2 * d + 1 : ℕ) : ℝ) / (2 * n)) :=
          mul_le_mul ih' hratio hratio_nonneg
            (mul_nonneg (by
                unfold evenSymmetricMass symBinomialMass
                positivity)
              (Real.exp_pos _).le)
        _ = evenSymmetricMass n 0 *
            Real.exp (-(((d + 1 : ℕ) : ℝ) ^ 2) / (2 * n)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
          field_simp
          ring

/-- The product coefficient is bounded by a Gaussian at the larger of its
two diagonal offsets. -/
theorem fourierProductMass_gaussian_le {n d e : ℕ} (hn : 0 < n)
    (hd : d ≤ n) (he : e ≤ n) :
    fourierProductMass n d e ≤ planarReturnProbability n *
      Real.exp (-((max d e : ℕ) : ℝ) ^ 2 / (2 * n)) := by
  have hdexp := evenSymmetricMass_le_center_mul_exp hn hd
  have heexp := evenSymmetricMass_le_center_mul_exp hn he
  have hd0 : 0 ≤ evenSymmetricMass n d := by
    unfold evenSymmetricMass symBinomialMass
    positivity
  have he0 : 0 ≤ evenSymmetricMass n e := by
    unfold evenSymmetricMass symBinomialMass
    positivity
  have hc0 : 0 ≤ evenSymmetricMass n 0 := by
    unfold evenSymmetricMass symBinomialMass
    positivity
  rcases max_cases d e with ⟨hde, _⟩ | ⟨hed, _⟩
  · rw [hde]
    calc
      fourierProductMass n d e ≤
          (evenSymmetricMass n 0 * Real.exp (-((d : ℝ) ^ 2) / (2 * n))) *
            evenSymmetricMass n 0 := by
        unfold fourierProductMass
        exact mul_le_mul hdexp (evenSymmetricMass_le_center n e) he0
          (by positivity)
      _ = planarReturnProbability n * Real.exp (-((d : ℝ) ^ 2) / (2 * n)) := by
        rw [← fourierProductMass_center]
        unfold fourierProductMass
        ring
  · rw [hed]
    calc
      fourierProductMass n d e ≤ evenSymmetricMass n 0 *
          (evenSymmetricMass n 0 * Real.exp (-((e : ℝ) ^ 2) / (2 * n))) := by
        unfold fourierProductMass
        exact mul_le_mul (evenSymmetricMass_le_center n d) heexp he0 hc0
      _ = planarReturnProbability n * Real.exp (-((e : ℝ) ^ 2) / (2 * n)) := by
        rw [← fourierProductMass_center]
        unfold fourierProductMass
        ring

theorem fourierProductMass_eq_zero_of_lt_left {n d e : ℕ} (hnd : n < d) :
    fourierProductMass n d e = 0 := by
  unfold fourierProductMass evenSymmetricMass symBinomialMass
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem fourierProductMass_eq_zero_of_lt_right {n d e : ℕ} (hne : n < e) :
    fourierProductMass n d e = 0 := by
  unfold fourierProductMass evenSymmetricMass symBinomialMass
  have hz : (2 * n).choose (n + e) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [hz]
  simp

theorem fourierProductMass_eq_zero_of_lt_max {n d e : ℕ}
    (hn : n < max d e) : fourierProductMass n d e = 0 := by
  rw [lt_max_iff] at hn
  rcases hn with hn | hn
  · exact fourierProductMass_eq_zero_of_lt_left hn
  · exact fourierProductMass_eq_zero_of_lt_right hn

lemma exp_neg_le_two_div_sq {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 2 / x ^ 2 := by
  have hquad := Real.quadratic_le_exp_of_nonneg hx.le
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos x) (sq_pos_of_pos hx)).2
  nlinarith

/-- The total off-centre mass before the diffusive scale `R²` is uniformly
bounded. -/
theorem sum_fourierProductMass_before_sq_le {d e : ℕ}
    (hR : 0 < max d e) :
    ∑ n ∈ Finset.range ((max d e) ^ 2), fourierProductMass n d e ≤ 8 := by
  let R := max d e
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hR2 : (0 : ℝ) < (R : ℝ) ^ 2 := sq_pos_of_pos hR0
  calc
    ∑ n ∈ Finset.range (R ^ 2), fourierProductMass n d e ≤
        ∑ _n ∈ Finset.range (R ^ 2), (8 : ℝ) / R ^ 2 := by
      apply Finset.sum_le_sum
      intro n hnmem
      by_cases hnR : n < R
      · rw [fourierProductMass_eq_zero_of_lt_max hnR]
        positivity
      · have hRn : R ≤ n := Nat.le_of_not_gt hnR
        have hn0 : 0 < n := hR.trans_le hRn
        have hd : d ≤ n := (le_max_left d e).trans hRn
        have he : e ≤ n := (le_max_right d e).trans hRn
        have hgauss := fourierProductMass_gaussian_le hn0 hd he
        have hx : (0 : ℝ) < (R : ℝ) ^ 2 / (2 * n) := by positivity
        have hexp := exp_neg_le_two_div_sq hx
        have hreturn := planarReturnProbability_upper_bound n
        have hmass0 : 0 ≤ fourierProductMass n d e := by
          unfold fourierProductMass evenSymmetricMass symBinomialMass
          positivity
        have hexp0 : 0 ≤ Real.exp (-((R : ℝ) ^ 2 / (2 * n))) :=
          (Real.exp_pos _).le
        calc
          fourierProductMass n d e ≤ planarReturnProbability n *
              Real.exp (-((R : ℝ) ^ 2 / (2 * n))) := by
            simpa only [R, neg_div] using hgauss
          _ ≤ (1 / (n + 1 : ℝ)) * Real.exp (-((R : ℝ) ^ 2 / (2 * n))) := by
            gcongr
          _ ≤ (1 / (n + 1 : ℝ)) *
              (2 / (((R : ℝ) ^ 2 / (2 * n)) ^ 2)) := by
            gcongr
          _ ≤ 8 / R ^ 2 := by
            have hnlt : n < R ^ 2 := Finset.mem_range.mp hnmem
            have hnR2 : (n : ℝ) ≤ R ^ 2 := by exact_mod_cast hnlt.le
            field_simp
            nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((R : ℝ) ^ 2 - n)]
    _ = 8 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
      field_simp [hR2.ne']

/-! ## The central Fourier coefficient and the harmonic main term -/

/-- Robbins' error gives an exact exponential formula for the return
coefficient. -/
theorem planarReturnProbability_eq_exp_error {n : ℕ} (hn : 0 < n) :
    planarReturnProbability n =
      Real.exp (2 * centralBinomialLogError n) / (Real.pi * n) := by
  have hq := centralBinom_normalized_eq_exp_error (Nat.ne_of_gt hn)
  have hsq :
      ((Nat.centralBinom n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n) ^ 2 =
        Real.exp (2 * centralBinomialLogError n) := by
    rw [hq]
    simpa [mul_comm] using (Real.exp_nat_mul (centralBinomialLogError n) 2).symm
  rw [← hsq]
  unfold planarReturnProbability
  have hsqrt : Real.sqrt (Real.pi * n) ^ 2 = Real.pi * n :=
    Real.sq_sqrt (by positivity)
  have hpow : ((4 : ℝ) ^ n) ^ 2 = 16 ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [div_pow, mul_pow, hsqrt, hpow]
  field_simp

/-- The return coefficient differs from `1/(πn)` by a summable error. -/
theorem abs_planarReturnProbability_sub_main_le {n : ℕ} (hn : 0 < n) :
    |planarReturnProbability n - 1 / (Real.pi * n)| ≤ 1 / (n : ℝ) ^ 2 := by
  have herr := centralBinomialLogError_robbins_bounds (Nat.ne_of_gt hn)
  have hnR : (0 : ℝ) < n := by positivity
  have hA : |2 * centralBinomialLogError n| ≤ 1 / (n : ℝ) := by
    rw [abs_le]
    constructor
    · calc
        -(1 / (n : ℝ)) ≤ 2 * (-(2 * ((1 : ℝ) / (12 * n)))) := by
          field_simp
          nlinarith
        _ ≤ 2 * centralBinomialLogError n := by linarith [herr.1]
    · calc
        2 * centralBinomialLogError n ≤ 2 * ((1 : ℝ) / (12 * (2 * n))) := by
          linarith [herr.2]
        _ ≤ 1 / (n : ℝ) := by
          field_simp
          nlinarith
  have hAone : |2 * centralBinomialLogError n| ≤ 1 :=
    hA.trans (by
      rw [div_le_one hnR]
      exact_mod_cast hn)
  have hexp := Real.abs_exp_sub_one_le hAone
  rw [planarReturnProbability_eq_exp_error hn]
  have hden : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  calc
    |Real.exp (2 * centralBinomialLogError n) / (Real.pi * n) -
        1 / (Real.pi * n)| =
        |(Real.exp (2 * centralBinomialLogError n) - 1) /
          (Real.pi * n)| := by
      congr 1
      field_simp
    _ = |Real.exp (2 * centralBinomialLogError n) - 1| /
        (Real.pi * n) := by
      rw [abs_div, abs_of_pos hden]
    _ ≤ (2 * |2 * centralBinomialLogError n|) / (Real.pi * n) := by
      exact div_le_div_of_nonneg_right hexp hden.le
    _ ≤ (2 * (1 / (n : ℝ))) / (Real.pi * n) := by
      gcongr
    _ ≤ 1 / (n : ℝ) ^ 2 := by
      have hpi := Real.two_le_pi
      field_simp
      nlinarith

/-- Harmonic comparison term, indexed from zero. -/
noncomputable def returnHarmonicTerm (n : ℕ) : ℝ :=
  1 / (Real.pi * (n + 1 : ℝ))

theorem sum_returnHarmonicTerm (M : ℕ) :
    ∑ n ∈ Finset.range M, returnHarmonicTerm n =
      (1 / Real.pi) * (harmonic M : ℝ) := by
  calc
    ∑ n ∈ Finset.range M, returnHarmonicTerm n =
        (1 / Real.pi) * ∑ n ∈ Finset.range M, (1 / (n + 1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      unfold returnHarmonicTerm
      field_simp [ne_of_gt Real.pi_pos]
    _ = (1 / Real.pi) * (harmonic M : ℝ) := by
      simp [harmonic, one_div]

theorem abs_planarReturnProbability_sub_harmonicTerm_le {n : ℕ} (hn : 0 < n) :
    |planarReturnProbability n - returnHarmonicTerm n| ≤ 2 / (n : ℝ) ^ 2 := by
  have hmain := abs_planarReturnProbability_sub_main_le hn
  have hnR : (0 : ℝ) < n := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  calc
    |planarReturnProbability n - returnHarmonicTerm n| ≤
        |planarReturnProbability n - 1 / (Real.pi * n)| +
          |1 / (Real.pi * n) - returnHarmonicTerm n| := by
      rw [show planarReturnProbability n - returnHarmonicTerm n =
        (planarReturnProbability n - 1 / (Real.pi * n)) +
          (1 / (Real.pi * n) - returnHarmonicTerm n) by ring]
      exact abs_add_le
        (planarReturnProbability n - 1 / (Real.pi * n))
        (1 / (Real.pi * n) - returnHarmonicTerm n)
    _ ≤ 1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 := by
      gcongr
      unfold returnHarmonicTerm
      rw [abs_of_nonneg]
      · have hpiOne : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
        field_simp
        nlinarith
      · apply sub_nonneg.mpr
        exact one_div_le_one_div_of_le (by positivity) (by
          have : Real.pi * (n : ℝ) ≤ Real.pi * (n + 1 : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
            norm_num
          exact this)
    _ = 2 / (n : ℝ) ^ 2 := by ring

lemma abs_planarReturnProbability_zero_sub_harmonicTerm_le :
    |planarReturnProbability 0 - returnHarmonicTerm 0| ≤ 1 := by
  have hpiOne : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hinv : (1 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    exact hpiOne
  have hinv0 : 0 ≤ (1 : ℝ) / Real.pi := by positivity
  have hinv' : Real.pi⁻¹ ≤ (1 : ℝ) := by simpa [one_div] using hinv
  have hinv0' : 0 ≤ Real.pi⁻¹ := by simpa [one_div] using hinv0
  norm_num [planarReturnProbability, Nat.centralBinom, returnHarmonicTerm]
  rw [abs_of_nonneg]
  · linarith
  · linarith

/-- The complete finite return sum differs from its harmonic main term by an
absolute constant. -/
theorem abs_sum_planarReturnProbability_sub_harmonic_le (M : ℕ) :
    |(∑ n ∈ Finset.range M, planarReturnProbability n) -
        (1 / Real.pi) * (harmonic M : ℝ)| ≤ 5 := by
  rw [← sum_returnHarmonicTerm]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ n ∈ Finset.range M,
        (planarReturnProbability n - returnHarmonicTerm n)| ≤
        ∑ n ∈ Finset.range M,
          |planarReturnProbability n - returnHarmonicTerm n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ 5 := by
      by_cases hM : M = 0
      · subst M
        simp
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
        have hrange : Finset.range M = insert 0 (Finset.Ioo 0 M) := by
          ext n
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
          omega
        rw [hrange, Finset.sum_insert (by simp)]
        calc
          |planarReturnProbability 0 - returnHarmonicTerm 0| +
              ∑ n ∈ Finset.Ioo 0 M,
                |planarReturnProbability n - returnHarmonicTerm n| ≤
              1 + ∑ n ∈ Finset.Ioo 0 M, (2 / (n : ℝ) ^ 2) := by
            gcongr
            · exact abs_planarReturnProbability_zero_sub_harmonicTerm_le
            · exact abs_planarReturnProbability_sub_harmonicTerm_le
                (Finset.mem_Ioo.mp ‹_›).1
          _ = 1 + 2 * ∑ n ∈ Finset.Ioo 0 M, ((n : ℝ) ^ 2)⁻¹ := by
            rw [Finset.mul_sum]
            apply congrArg (1 + ·)
            apply Finset.sum_congr rfl
            intro n _
            rw [div_eq_mul_inv]
          _ ≤ 1 + 2 * 2 := by
            gcongr
            simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 M)
          _ = 5 := by norm_num

/-- The central return sum has the sharp logarithmic coefficient. -/
theorem abs_sum_planarReturnProbability_sub_log_le {M : ℕ} (hM : 0 < M) :
    |(∑ n ∈ Finset.range M, planarReturnProbability n) -
        (1 / Real.pi) * Real.log M| ≤ 6 := by
  have hsum := abs_sum_planarReturnProbability_sub_harmonic_le M
  have hloglower : Real.log (M : ℝ) ≤ (harmonic M : ℝ) := by
    calc
      Real.log (M : ℝ) ≤ Real.log (M + 1 : ℕ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast (Nat.le_succ M)
      _ ≤ (harmonic M : ℝ) := by exact_mod_cast log_add_one_le_harmonic M
  have hlogupper : (harmonic M : ℝ) ≤ 1 + Real.log (M : ℝ) := by
    exact_mod_cast harmonic_le_one_add_log M
  have hpiInv : (1 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    exact le_trans (by norm_num) Real.two_le_pi
  have hharm : |(1 / Real.pi) * (harmonic M : ℝ) -
      (1 / Real.pi) * Real.log M| ≤ 1 := by
    rw [abs_of_nonneg]
    · calc
        (1 / Real.pi) * (harmonic M : ℝ) -
            (1 / Real.pi) * Real.log M =
            (1 / Real.pi) * ((harmonic M : ℝ) - Real.log M) := by ring
        _ ≤ (1 / Real.pi) * 1 := by gcongr; linarith
        _ ≤ 1 := by simpa using hpiInv
    · have hpi0 : 0 ≤ (1 : ℝ) / Real.pi := by positivity
      nlinarith
  calc
    |(∑ n ∈ Finset.range M, planarReturnProbability n) -
        (1 / Real.pi) * Real.log M| ≤
        |(∑ n ∈ Finset.range M, planarReturnProbability n) -
          (1 / Real.pi) * (harmonic M : ℝ)| +
        |(1 / Real.pi) * (harmonic M : ℝ) -
          (1 / Real.pi) * Real.log M| := by
      rw [show (∑ n ∈ Finset.range M, planarReturnProbability n) -
          (1 / Real.pi) * Real.log M =
          ((∑ n ∈ Finset.range M, planarReturnProbability n) -
            (1 / Real.pi) * (harmonic M : ℝ)) +
          ((1 / Real.pi) * (harmonic M : ℝ) -
            (1 / Real.pi) * Real.log M) by ring]
      exact abs_add_le _ _
    _ ≤ 5 + 1 := add_le_add hsum hharm
    _ = 6 := by norm_num

/-! ## Assembly of the potential asymptotic -/

theorem sum_fourierProductLoss_eq_sub (M d e : ℕ) :
    ∑ n ∈ Finset.range M, fourierProductLoss d e n =
      (∑ n ∈ Finset.range M, planarReturnProbability n) -
        ∑ n ∈ Finset.range M, fourierProductMass n d e := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold fourierProductLoss
  rw [fourierProductMass_center]

theorem fourierPotential_split (M d e : ℕ) :
    fourierPotential d e =
      (∑ n ∈ Finset.range M, fourierProductLoss d e n) +
        ∑' n : ℕ, fourierProductLoss d e (n + M) := by
  exact (Summable.sum_add_tsum_nat_add M (summable_fourierProductLoss d e)).symm

theorem tsum_fourierProductLoss_sq_tail_nonneg {d e : ℕ} :
    0 ≤ ∑' n : ℕ, fourierProductLoss d e (n + (max d e) ^ 2) := by
  exact tsum_nonneg fun n ↦ fourierProductLoss_nonneg d e _

theorem tsum_fourierProductLoss_sq_tail_le {d e : ℕ}
    (hR : 0 < max d e) :
    ∑' n : ℕ, fourierProductLoss d e (n + (max d e) ^ 2) ≤ 80 := by
  let R := max d e
  have hR2nat : 0 < R ^ 2 := by positivity
  have hraw := tsum_fourierProductLoss_shift_le (d := d) (e := e) hR2nat
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hR2 : (0 : ℝ) < (R : ℝ) ^ 2 := sq_pos_of_pos hR0
  have hd : d ≤ R := le_max_left d e
  have he : e ≤ R := le_max_right d e
  have hd1 : (d + 1 : ℝ) ≤ 2 * R := by
    have : d + 1 ≤ 2 * R := by omega
    exact_mod_cast this
  have he1 : (e + 1 : ℝ) ≤ 2 * R := by
    have : e + 1 ≤ 2 * R := by omega
    exact_mod_cast this
  have hd10 : (0 : ℝ) ≤ d + 1 := by positivity
  have he10 : (0 : ℝ) ≤ e + 1 := by positivity
  have hnum : 10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) ≤
      80 * (R : ℝ) ^ 2 := by
    nlinarith [sq_le_sq₀ hd10 (by positivity : (0 : ℝ) ≤ 2 * R) |>.2 hd1,
      sq_le_sq₀ he10 (by positivity : (0 : ℝ) ≤ 2 * R) |>.2 he1]
  calc
    ∑' n : ℕ, fourierProductLoss d e (n + R ^ 2) ≤
        10 * ((d + 1 : ℝ) ^ 2 + (e + 1 : ℝ) ^ 2) / (R ^ 2 : ℕ) := by
      simpa [R] using hraw
    _ ≤ 80 := by
      norm_num only [Nat.cast_pow]
      rw [div_le_iff₀ hR2]
      simpa [mul_comm] using hnum

/-- The finite potential through the diffusive scale already has the sharp
logarithmic main term. -/
theorem abs_sum_fourierProductLoss_sq_sub_log_le {d e : ℕ}
    (hR : 0 < max d e) :
    |(∑ n ∈ Finset.range ((max d e) ^ 2), fourierProductLoss d e n) -
        (1 / Real.pi) * Real.log (((max d e) ^ 2 : ℕ) : ℝ)| ≤ 14 := by
  let R := max d e
  let M := R ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hreturn := abs_sum_planarReturnProbability_sub_log_le hM
  have hmass := sum_fourierProductMass_before_sq_le hR
  have hmass0 : 0 ≤ ∑ n ∈ Finset.range M, fourierProductMass n d e := by
    exact Finset.sum_nonneg fun n _ ↦ by
      unfold fourierProductMass evenSymmetricMass symBinomialMass
      positivity
  rw [sum_fourierProductLoss_eq_sub]
  calc
    |((∑ n ∈ Finset.range M, planarReturnProbability n) -
          ∑ n ∈ Finset.range M, fourierProductMass n d e) -
        (1 / Real.pi) * Real.log (M : ℝ)| ≤
        |(∑ n ∈ Finset.range M, planarReturnProbability n) -
          (1 / Real.pi) * Real.log (M : ℝ)| +
          |-(∑ n ∈ Finset.range M, fourierProductMass n d e)| := by
      rw [show ((∑ n ∈ Finset.range M, planarReturnProbability n) -
            ∑ n ∈ Finset.range M, fourierProductMass n d e) -
          (1 / Real.pi) * Real.log (M : ℝ) =
          ((∑ n ∈ Finset.range M, planarReturnProbability n) -
            (1 / Real.pi) * Real.log (M : ℝ)) +
          (-(∑ n ∈ Finset.range M, fourierProductMass n d e)) by ring]
      exact abs_add_le _ _
    _ ≤ 6 + 8 := by
      rw [abs_neg, abs_of_nonneg hmass0]
      exact add_le_add hreturn (by simpa [M, R] using hmass)
    _ = 14 := by norm_num

/-- **Sharp uniform planar potential asymptotic.**  In diagonal Fourier
coordinates and max norm, the error in `(2/π) log R` is bounded by the
absolute constant `100`. -/
theorem diagonalPotential_log_asymptotic_bound {d e : ℕ}
    (hR : 0 < max d e) :
    |fourierPotential d e -
        (2 / Real.pi) * Real.log (max d e : ℝ)| ≤ 100 := by
  let R := max d e
  let M := R ^ 2
  have hprefix := abs_sum_fourierProductLoss_sq_sub_log_le (d := d) (e := e) hR
  have htail := tsum_fourierProductLoss_sq_tail_le (d := d) (e := e) hR
  have htail0 := tsum_fourierProductLoss_sq_tail_nonneg (d := d) (e := e)
  have hsplit := fourierPotential_split M d e
  have hlog : (1 / Real.pi) * Real.log (M : ℝ) =
      (2 / Real.pi) * Real.log (R : ℝ) := by
    dsimp [M]
    norm_num only [Nat.cast_pow]
    rw [Real.log_pow]
    ring
  rw [hsplit, show max (d : ℝ) (e : ℝ) = (R : ℝ) by norm_num [R], ← hlog]
  calc
    |((∑ n ∈ Finset.range M, fourierProductLoss d e n) +
          ∑' n : ℕ, fourierProductLoss d e (n + M)) -
        (1 / Real.pi) * Real.log (M : ℝ)| ≤
        |(∑ n ∈ Finset.range M, fourierProductLoss d e n) -
          (1 / Real.pi) * Real.log (M : ℝ)| +
          |∑' n : ℕ, fourierProductLoss d e (n + M)| := by
      rw [show ((∑ n ∈ Finset.range M, fourierProductLoss d e n) +
            ∑' n : ℕ, fourierProductLoss d e (n + M)) -
          (1 / Real.pi) * Real.log (M : ℝ) =
          ((∑ n ∈ Finset.range M, fourierProductLoss d e n) -
            (1 / Real.pi) * Real.log (M : ℝ)) +
          (∑' n : ℕ, fourierProductLoss d e (n + M)) by ring]
      exact abs_add_le _ _
    _ ≤ 14 + 80 := by
      apply add_le_add
      · simpa [M, R] using hprefix
      · have ht0 : 0 ≤ ∑' n : ℕ, fourierProductLoss d e (n + M) := by
          simpa [M, R] using htail0
        rw [abs_of_nonneg ht0]
        simpa [M, R] using htail
    _ ≤ 100 := by norm_num

end PotentialFourierIntegral
end Erdos1165
