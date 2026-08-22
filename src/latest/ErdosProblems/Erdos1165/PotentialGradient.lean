/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.PotentialAsymptotic

/-!
# Quantitative gradient bounds for the planar potential kernel

This file proves the discrete estimate behind the annular Harnack bounds.
In diagonal coordinates the potential is a series of products of centered
binomial masses.  The exact adjacent-binomial ratio turns an adjacent
potential difference into a positive series.  A cubic exponential bound up
to the diffusive scale and a telescoping reciprocal-square tail then give an
explicit `O(1/R)` estimate.
-/

open Filter Real
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialGradient

open BinomialGaussian EndpointDiagonal PotentialKernel PotentialConvergence
  PotentialFourierIntegral PotentialAsymptotic

/-- The positive summand in the first-coordinate discrete derivative. -/
noncomputable def firstGradientTerm (d e n : ℕ) : ℝ :=
  (evenSymmetricMass n d - evenSymmetricMass n (d + 1)) *
    evenSymmetricMass n e

lemma evenSymmetricMass_succ_mul_le {n d : ℕ} (hd : d ≤ n) :
    evenSymmetricMass n (d + 1) * (n + d + 1 : ℝ) =
      evenSymmetricMass n d * (n - d : ℝ) := by
  by_cases hdn : d < n
  · exact evenSymmetricMass_succ_mul hdn
  · have hdeq : d = n := by omega
    subst d
    unfold evenSymmetricMass symBinomialMass
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Exact adjacent-ratio formula, including the boundary case `d=n`. -/
theorem firstGradientTerm_eq {d e n : ℕ} (hd : d ≤ n) :
    firstGradientTerm d e n = fourierProductMass n d e *
      (((2 * d + 1 : ℕ) : ℝ) / (n + d + 1 : ℝ)) := by
  have hrec := evenSymmetricMass_succ_mul_le (n := n) hd
  have hden : (0 : ℝ) < n + d + 1 := by positivity
  unfold firstGradientTerm fourierProductMass
  rw [show evenSymmetricMass n (d + 1) =
      evenSymmetricMass n d * ((n - d : ℝ) / (n + d + 1)) by
    field_simp [hden.ne']
    exact hrec]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp [hden.ne']
  ring

theorem firstGradientTerm_eq_zero_of_lt {d e n : ℕ} (hn : n < d) :
    firstGradientTerm d e n = 0 := by
  unfold firstGradientTerm evenSymmetricMass symBinomialMass
  rw [Nat.choose_eq_zero_of_lt (by omega),
    Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem firstGradientTerm_nonneg (d e n : ℕ) :
    0 ≤ firstGradientTerm d e n := by
  by_cases hd : d ≤ n
  · rw [firstGradientTerm_eq hd]
    exact mul_nonneg
      (by unfold fourierProductMass evenSymmetricMass symBinomialMass; positivity)
      (div_nonneg (by positivity) (by positivity))
  · rw [firstGradientTerm_eq_zero_of_lt (Nat.lt_of_not_ge hd)]

/-- The cubic Taylor term yields a convenient polynomial majorant for the
negative exponential. -/
lemma exp_neg_le_six_div_cube {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 6 / x ^ 3 := by
  have hcubic : x ^ 3 / 6 ≤ Real.exp x := by
    have h := Real.pow_div_factorial_le_exp x hx.le 3
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos x) (pow_pos hx 3)).2
  nlinarith

/-- Before the diffusive scale, an adjacent derivative summand has a
polynomial majorant whose sum is `O(1/R)`. -/
theorem firstGradientTerm_before_sq_le {d e n : ℕ}
    (hR : 0 < max d e) (hn : n < (max d e) ^ 2) :
    firstGradientTerm d e n ≤
      144 * (n : ℝ) / (↑(max d e) : ℝ) ^ 5 := by
  let R := max d e
  change firstGradientTerm d e n ≤ 144 * (n : ℝ) / (R : ℝ) ^ 5
  by_cases hnR : n < R
  · by_cases hnd : n < d
    · rw [firstGradientTerm_eq_zero_of_lt hnd]
      positivity
    · have hne : n < e := by
        have : n < max d e := hnR
        omega
      have hezero : evenSymmetricMass n e = 0 := by
        unfold evenSymmetricMass symBinomialMass
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [show firstGradientTerm d e n = 0 by simp [firstGradientTerm, hezero]]
      have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
      positivity
  · have hRn : R ≤ n := Nat.le_of_not_gt hnR
    have hn0 : 0 < n := hR.trans_le hRn
    have hd : d ≤ n := (le_max_left d e).trans hRn
    have he : e ≤ n := (le_max_right d e).trans hRn
    rw [firstGradientTerm_eq hd]
    have hgauss := fourierProductMass_gaussian_le hn0 hd he
    have hx : (0 : ℝ) < (R : ℝ) ^ 2 / (2 * n) := by positivity
    have hexp := exp_neg_le_six_div_cube hx
    have hreturn := planarReturnProbability_upper_bound n
    have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
    have hnRreal : (R : ℝ) ≤ n := by exact_mod_cast hRn
    have hdR : (d : ℝ) ≤ R := by exact_mod_cast le_max_left d e
    have hfactor : (((2 * d + 1 : ℕ) : ℝ) / (n + d + 1 : ℝ)) ≤
        3 * R / n := by
      have hnum : (((2 * d + 1 : ℕ) : ℝ)) ≤ 3 * R := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        have hRone : (1 : ℝ) ≤ R := by exact_mod_cast hR
        linarith
      have hden : (n : ℝ) ≤ n + d + 1 := by linarith
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
      have hbigpos : (0 : ℝ) < n + d + 1 := by positivity
      calc
        (((2 * d + 1 : ℕ) : ℝ) / (n + d + 1 : ℝ)) ≤
            (((2 * d + 1 : ℕ) : ℝ) / n) :=
          div_le_div_of_nonneg_left (by positivity) hnpos hden
      _ ≤ 3 * R / n := div_le_div_of_nonneg_right hnum hnpos.le
    have hmassgauss : fourierProductMass n d e ≤
        planarReturnProbability n * Real.exp (-((R : ℝ) ^ 2 / (2 * n))) := by
      simpa only [R, neg_div] using hgauss
    have hfactor0 : 0 ≤ (((2 * d + 1 : ℕ) : ℝ) / (n + d + 1 : ℝ)) := by
      exact div_nonneg (by positivity) (by positivity)
    have hgauss0 : 0 ≤ planarReturnProbability n *
        Real.exp (-((R : ℝ) ^ 2 / (2 * n))) := by
      apply mul_nonneg _ (Real.exp_pos _).le
      unfold planarReturnProbability
      positivity
    calc
      fourierProductMass n d e * (((2 * d + 1 : ℕ) : ℝ) /
          (n + d + 1 : ℝ)) ≤
          (planarReturnProbability n *
            Real.exp (-((R : ℝ) ^ 2 / (2 * n)))) * (3 * R / n) :=
        mul_le_mul hmassgauss hfactor hfactor0 hgauss0
      _ ≤ ((1 / (n + 1 : ℝ)) *
            (6 / (((R : ℝ) ^ 2 / (2 * n)) ^ 3))) * (3 * R / n) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hreturn hexp (Real.exp_pos _).le (by positivity)
      _ ≤ 144 * (n : ℝ) / (R : ℝ) ^ 5 := by
        have hnlt : n < R ^ 2 := by simpa only [R] using hn
        have hnR2 : (n : ℝ) ≤ R ^ 2 := by exact_mod_cast hnlt.le
        field_simp
        nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((R : ℝ) ^ 2 - n)]

/-- After the diffusive scale, the return-probability envelope is summable
and gives the remaining `O(1/R)` contribution. -/
theorem firstGradientTerm_after_sq_le {d e n : ℕ}
    (hR : 0 < max d e) (hn : (max d e) ^ 2 ≤ n) :
    firstGradientTerm d e n ≤
      3 * (↑(max d e) : ℝ) / ((n : ℝ) * (n + 1)) := by
  let R := max d e
  change firstGradientTerm d e n ≤ 3 * (R : ℝ) / ((n : ℝ) * (n + 1))
  have hRpos : 0 < R := by simpa only [R] using hR
  have hRn : R ≤ n := by
    have hRR : R ≤ R ^ 2 := by nlinarith
    exact hRR.trans (by simpa only [R] using hn)
  have hn0 : 0 < n := hR.trans_le hRn
  have hd : d ≤ n := (le_max_left d e).trans hRn
  rw [firstGradientTerm_eq hd]
  have hmass : fourierProductMass n d e ≤ planarReturnProbability n := by
    unfold fourierProductMass
    rw [← fourierProductMass_center]
    exact mul_le_mul (evenSymmetricMass_le_center n d)
      (evenSymmetricMass_le_center n e)
      (by unfold evenSymmetricMass symBinomialMass; positivity)
      (by unfold evenSymmetricMass symBinomialMass; positivity)
  have hreturn := planarReturnProbability_upper_bound n
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hdR : (d : ℝ) ≤ R := by exact_mod_cast le_max_left d e
  have hfactor : (((2 * d + 1 : ℕ) : ℝ) / (n + d + 1 : ℝ)) ≤
      3 * R / n := by
    have hnum : (((2 * d + 1 : ℕ) : ℝ)) ≤ 3 * R := by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have hRone : (1 : ℝ) ≤ R := by exact_mod_cast hR
      linarith
    have hden : (n : ℝ) ≤ n + d + 1 := by linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hbigpos : (0 : ℝ) < n + d + 1 := by positivity
    calc
      (((2 * d + 1 : ℕ) : ℝ) / (n + d + 1 : ℝ)) ≤
          (((2 * d + 1 : ℕ) : ℝ) / n) :=
        div_le_div_of_nonneg_left (by positivity) hnpos hden
      _ ≤ 3 * R / n := div_le_div_of_nonneg_right hnum hnpos.le
  calc
    fourierProductMass n d e * (((2 * d + 1 : ℕ) : ℝ) /
        (n + d + 1 : ℝ)) ≤ (1 / (n + 1 : ℝ)) * (3 * R / n) := by
      gcongr
      exact hmass.trans hreturn
    _ = 3 * R / ((n : ℝ) * (n + 1)) := by field_simp

theorem summable_firstGradientTerm (d e : ℕ) :
    Summable (firstGradientTerm d e) := by
  have h₁ := summable_fourierProductLoss d e
  have h₂ := summable_fourierProductLoss (d + 1) e
  have hsub := h₂.sub h₁
  apply hsub.congr
  intro n
  unfold firstGradientTerm fourierProductLoss fourierProductMass
  ring

/-- The adjacent potential increment is the positive gradient series. -/
theorem fourierPotential_succ_sub (d e : ℕ) :
    fourierPotential (d + 1) e - fourierPotential d e =
      ∑' n : ℕ, firstGradientTerm d e n := by
  unfold fourierPotential
  rw [← Summable.tsum_sub (summable_fourierProductLoss (d + 1) e)
    (summable_fourierProductLoss d e)]
  apply tsum_congr
  intro n
  unfold firstGradientTerm fourierProductLoss fourierProductMass
  ring

private lemma sum_nat_cast_range_le_sq (M : ℕ) :
    ∑ n ∈ Finset.range M, (n : ℝ) ≤ (M : ℝ) ^ 2 := by
  calc
    ∑ n ∈ Finset.range M, (n : ℝ) ≤ ∑ _n ∈ Finset.range M, (M : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact_mod_cast (Finset.mem_range.mp hn).le
    _ = (M : ℝ) ^ 2 := by
      simp [pow_two]

/-- Explicit adjacent-coordinate potential gradient. -/
theorem fourierPotential_succ_sub_le {d e : ℕ} (hR : 0 < max d e) :
    0 ≤ fourierPotential (d + 1) e - fourierPotential d e ∧
      fourierPotential (d + 1) e - fourierPotential d e ≤
        150 / (↑(max d e) : ℝ) := by
  let R := max d e
  let M := R ^ 2
  have hsum := summable_firstGradientTerm d e
  rw [fourierPotential_succ_sub]
  constructor
  · exact tsum_nonneg (firstGradientTerm_nonneg d e)
  · change (∑' n : ℕ, firstGradientTerm d e n) ≤ 150 / (R : ℝ)
    rw [← hsum.sum_add_tsum_nat_add M]
    have hprefix : ∑ n ∈ Finset.range M, firstGradientTerm d e n ≤
        144 / (R : ℝ) := by
      calc
        ∑ n ∈ Finset.range M, firstGradientTerm d e n ≤
            ∑ n ∈ Finset.range M, 144 * (n : ℝ) / (R : ℝ) ^ 5 := by
          apply Finset.sum_le_sum
          intro n hn
          simpa only [R] using firstGradientTerm_before_sq_le hR (by
            simpa only [M, R] using Finset.mem_range.mp hn)
        _ = 144 / (R : ℝ) ^ 5 * ∑ n ∈ Finset.range M, (n : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        _ ≤ 144 / (R : ℝ) ^ 5 * (M : ℝ) ^ 2 := by
          gcongr
          exact sum_nat_cast_range_le_sq M
        _ = 144 / (R : ℝ) := by
          dsimp [M]
          norm_num only [Nat.cast_pow]
          have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
          field_simp
    have htail : ∑' n : ℕ, firstGradientTerm d e (n + M) ≤
        3 / (R : ℝ) := by
      have hcomp := PotentialFourierIntegral.hasSum_inverse_nat_mul_succ_shift
        (show 0 < M by dsimp [M]; positivity)
      have hscomp := hcomp.summable.mul_left (3 * (R : ℝ))
      calc
        ∑' n : ℕ, firstGradientTerm d e (n + M) ≤
            ∑' n : ℕ, (3 * (R : ℝ)) *
              (1 / (((n + M : ℕ) : ℝ) * (n + M + 1))) := by
          apply Summable.tsum_le_tsum _
            ((summable_nat_add_iff M).mpr hsum) hscomp
          intro n
          have h := firstGradientTerm_after_sq_le hR
            (show R ^ 2 ≤ n + M by dsimp [M]; omega)
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, M, R] using h
        _ = (3 * (R : ℝ)) * (1 / (M : ℝ)) := hcomp.mul_left _ |>.tsum_eq
        _ = 3 / (R : ℝ) := by
          dsimp [M]
          norm_num only [Nat.cast_pow]
          have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
          field_simp
    calc
      (∑ n ∈ Finset.range M, firstGradientTerm d e n) +
          ∑' n : ℕ, firstGradientTerm d e (n + M) ≤
          144 / (R : ℝ) + 3 / (R : ℝ) := add_le_add hprefix htail
      _ ≤ 150 / (R : ℝ) := by
        have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
        calc
          144 / (R : ℝ) + 3 / (R : ℝ) = 147 / R := by ring
          _ ≤ 150 / R := div_le_div_of_nonneg_right (by norm_num) hR0.le

/-- Symmetry of the diagonal-coordinate potential. -/
theorem fourierPotential_comm (d e : ℕ) :
    fourierPotential d e = fourierPotential e d := by
  unfold fourierPotential
  apply tsum_congr
  intro n
  unfold fourierProductLoss fourierProductMass
  ring

/-- The same adjacent estimate in the second diagonal coordinate. -/
theorem fourierPotential_second_succ_sub_le {d e : ℕ} (hR : 0 < max d e) :
    0 ≤ fourierPotential d (e + 1) - fourierPotential d e ∧
      fourierPotential d (e + 1) - fourierPotential d e ≤
        150 / (↑(max d e) : ℝ) := by
  rw [fourierPotential_comm d (e + 1), fourierPotential_comm d e,
    max_comm d e]
  exact fourierPotential_succ_sub_le (by simpa [max_comm] using hR)

/-- Telescoping the adjacent bound gives a finite-displacement gradient
estimate.  The denominator is the radius of the starting point; increasing a
coordinate only improves all later adjacent bounds. -/
theorem fourierPotential_add_sub_le {d e k : ℕ} (hR : 0 < max d e) :
    0 ≤ fourierPotential (d + k) e - fourierPotential d e ∧
      fourierPotential (d + k) e - fourierPotential d e ≤
        150 * (k : ℝ) / (↑(max d e) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hRk : 0 < max (d + k) e :=
        hR.trans_le (max_le_max_right e (Nat.le_add_right d k))
      have hadj := fourierPotential_succ_sub_le hRk
      have hmax : max d e ≤ max (d + k) e :=
        max_le_max_right e (Nat.le_add_right d k)
      have hRreal : (0 : ℝ) < (max d e : ℕ) := by exact_mod_cast hR
      have hmaxreal : ((max d e : ℕ) : ℝ) ≤ (max (d + k) e : ℕ) := by
        exact_mod_cast hmax
      have hadj' : fourierPotential (d + k + 1) e - fourierPotential (d + k) e ≤
          150 / (↑(max d e) : ℝ) :=
        hadj.2.trans (div_le_div_of_nonneg_left (by norm_num) hRreal hmaxreal)
      constructor
      · rw [show d + (k + 1) = d + k + 1 by omega]
        linarith [ih.1, hadj.1]
      · rw [show d + (k + 1) = d + k + 1 by omega]
        calc
          fourierPotential (d + k + 1) e - fourierPotential d e =
              (fourierPotential (d + k + 1) e - fourierPotential (d + k) e) +
                (fourierPotential (d + k) e - fourierPotential d e) := by ring
          _ ≤ 150 / (↑(max d e) : ℝ) +
              150 * (k : ℝ) / (↑(max d e) : ℝ) := add_le_add hadj' ih.2
          _ = 150 * ((k + 1 : ℕ) : ℝ) / (↑(max d e) : ℝ) := by
            push_cast
            ring

/-- Ordered-coordinate form of the finite-displacement estimate. -/
theorem fourierPotential_sub_le_of_le {d d' e : ℕ} (hdd : d ≤ d')
    (hR : 0 < max d e) :
    0 ≤ fourierPotential d' e - fourierPotential d e ∧
      fourierPotential d' e - fourierPotential d e ≤
        150 * ((d' - d : ℕ) : ℝ) / (↑(max d e) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdd
  simpa using fourierPotential_add_sub_le (d := d) (e := e) (k := k) hR

/-- Ordered displacement in the second coordinate. -/
theorem fourierPotential_second_sub_le_of_le {d e e' : ℕ} (hee : e ≤ e')
    (hR : 0 < max d e) :
    0 ≤ fourierPotential d e' - fourierPotential d e ∧
      fourierPotential d e' - fourierPotential d e ≤
        150 * ((e' - e : ℕ) : ℝ) / (↑(max d e) : ℝ) := by
  rw [fourierPotential_comm d e', fourierPotential_comm d e, max_comm d e]
  simpa [max_comm] using
    fourierPotential_sub_le_of_le (d := e) (d' := e') (e := d) hee
      (by simpa [max_comm] using hR)

/-- Symmetric distance between two natural coordinates. -/
def natGap (a b : ℕ) : ℕ := max a b - min a b

@[simp] theorem natGap_self (a : ℕ) : natGap a a = 0 := by
  simp [natGap]

theorem natGap_eq_sub_of_le {a b : ℕ} (h : a ≤ b) : natGap a b = b - a := by
  simp [natGap, max_eq_right h, min_eq_left h]

theorem natGap_comm (a b : ℕ) : natGap a b = natGap b a := by
  simp [natGap, max_comm, min_comm]

/-- Moving an integer by two changes the half absolute value by at most one.
This elementary fact is the finite geometry behind the odd-parity bridge. -/
lemma natGap_half_natAbs_sub_one_add_one_le (z : ℤ) :
    natGap ((z - 1).natAbs / 2) ((z + 1).natAbs / 2) ≤ 1 := by
  have hab : (z - 1).natAbs ≤ (z + 1).natAbs + 2 := by
    calc
      (z - 1).natAbs = ((z + 1) - 2).natAbs := by ring_nf
      _ ≤ (z + 1).natAbs + (2 : ℤ).natAbs := Int.natAbs_sub_le _ _
      _ = (z + 1).natAbs + 2 := by norm_num
  have hba : (z + 1).natAbs ≤ (z - 1).natAbs + 2 := by
    calc
      (z + 1).natAbs = ((z - 1) - (-2)).natAbs := by ring_nf
      _ ≤ (z - 1).natAbs + (-2 : ℤ).natAbs := Int.natAbs_sub_le _ _
      _ = (z - 1).natAbs + 2 := by norm_num
  have hab' : (z - 1).natAbs / 2 ≤ ((z + 1).natAbs + 2) / 2 :=
    Nat.div_le_div_right hab
  have hba' : (z + 1).natAbs / 2 ≤ ((z - 1).natAbs + 2) / 2 :=
    Nat.div_le_div_right hba
  unfold natGap
  omega

lemma natGap_half_natAbs_add_neg_one_add_one_le (z : ℤ) :
    natGap ((-1 + z).natAbs / 2) ((1 + z).natAbs / 2) ≤ 1 := by
  convert natGap_half_natAbs_sub_one_add_one_le z using 1
  all_goals ring_nf

lemma natGap_half_natAbs_add_one_neg_one_le (z : ℤ) :
    natGap ((1 + z).natAbs / 2) ((-1 + z).natAbs / 2) ≤ 1 := by
  rw [natGap_comm]
  exact natGap_half_natAbs_add_neg_one_add_one_le z

/-- Any two even neighbors of the same odd lattice point differ by at most
two in total half-diagonal offset. -/
lemma neighbor_diagonalOffset_gap_le_two (x : Point) (d₀ d : Direction) :
    natGap (firstDiagonalOffset (x - directionVector d₀))
        (firstDiagonalOffset (x - directionVector d)) +
      natGap (secondDiagonalOffset (x - directionVector d₀))
        (secondDiagonalOffset (x - directionVector d)) ≤ 2 := by
  fin_cases d₀ <;> fin_cases d <;>
    simp only [directionVector, Prod.fst_sub, Prod.snd_sub,
      sub_zero, firstDiagonalOffset, secondDiagonalOffset] <;>
    ring_nf <;>
    (try simp only [natGap_self, zero_add, add_zero]) <;>
    have hp := natGap_half_natAbs_add_neg_one_add_one_le (x.1 + x.2) <;>
    have hp' := natGap_half_natAbs_add_one_neg_one_le (x.1 + x.2) <;>
    have hm := natGap_half_natAbs_add_neg_one_add_one_le (x.1 - x.2) <;>
    have hm' := natGap_half_natAbs_add_one_neg_one_le (x.1 - x.2) <;>
    ring_nf at hp hp' hm hm' <;>
    omega

lemma min_add_natGap (a b : ℕ) : min a b + natGap a b = max a b := by
  unfold natGap
  omega

lemma radius_le_first_floor_add_gap (d d' e : ℕ) :
    max d e ≤ max (min d d') e + natGap d d' := by
  apply max_le
  · calc
      d ≤ max d d' := le_max_left _ _
      _ = min d d' + natGap d d' := (min_add_natGap d d').symm
      _ ≤ max (min d d') e + natGap d d' :=
        Nat.add_le_add_right (le_max_left _ _) _
  · exact (le_max_right (min d d') e).trans (Nat.le_add_right _ _)

lemma radius_le_second_floor_add_gaps (d d' e e' : ℕ) :
    max d e ≤ max d' (min e e') + (natGap d d' + natGap e e') := by
  apply max_le
  · calc
      d ≤ max d d' := le_max_left _ _
      _ = min d d' + natGap d d' := (min_add_natGap d d').symm
      _ ≤ d' + natGap d d' := Nat.add_le_add_right (min_le_right _ _) _
      _ ≤ max d' (min e e') + (natGap d d' + natGap e e') := by omega
  · calc
      e ≤ max e e' := le_max_left _ _
      _ = min e e' + natGap e e' := (min_add_natGap e e').symm
      _ ≤ max d' (min e e') + (natGap d d' + natGap e e') := by omega

private lemma scaled_div_radius_mono {q ρ R : ℕ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    150 * (q : ℝ) / (R : ℝ) ≤ 150 * (q : ℝ) / (ρ : ℝ) := by
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hρ)
    (by exact_mod_cast hρR)

/-- Absolute first-coordinate difference, with an explicit lower bound on
the radius along the monotone coordinate segment. -/
theorem abs_fourierPotential_first_sub_le {d d' e ρ : ℕ}
    (hρ : 0 < ρ) (hfloor : ρ ≤ max (min d d') e) :
    |fourierPotential d' e - fourierPotential d e| ≤
      150 * (natGap d d' : ℝ) / (ρ : ℝ) := by
  rcases le_total d d' with hdd | hdd
  · have hbase : ρ ≤ max d e := by simpa [min_eq_left hdd] using hfloor
    have hbound := fourierPotential_sub_le_of_le hdd (lt_of_lt_of_le hρ hbase)
    rw [abs_of_nonneg hbound.1, natGap_eq_sub_of_le hdd]
    exact hbound.2.trans (scaled_div_radius_mono hρ hbase)
  · have hbase : ρ ≤ max d' e := by simpa [min_eq_right hdd] using hfloor
    have hbound := fourierPotential_sub_le_of_le hdd (lt_of_lt_of_le hρ hbase)
    rw [abs_sub_comm, abs_of_nonneg hbound.1, natGap_comm,
      natGap_eq_sub_of_le hdd]
    exact hbound.2.trans (scaled_div_radius_mono hρ hbase)

/-- Absolute second-coordinate difference, with an explicit lower bound on
the radius along the monotone coordinate segment. -/
theorem abs_fourierPotential_second_sub_le {d e e' ρ : ℕ}
    (hρ : 0 < ρ) (hfloor : ρ ≤ max d (min e e')) :
    |fourierPotential d e' - fourierPotential d e| ≤
      150 * (natGap e e' : ℝ) / (ρ : ℝ) := by
  rw [fourierPotential_comm d e', fourierPotential_comm d e]
  apply abs_fourierPotential_first_sub_le hρ
  simpa [max_comm] using hfloor

/-- Two-coordinate finite-difference estimate.  The hypotheses say that
`ρ` is a lower radius bound on the two monotone coordinate segments
`(d,e) → (d',e) → (d',e')`. -/
theorem abs_fourierPotential_sub_le {d e d' e' ρ : ℕ}
    (hρ : 0 < ρ)
    (hfirst : ρ ≤ max (min d d') e)
    (hsecond : ρ ≤ max d' (min e e')) :
    |fourierPotential d' e' - fourierPotential d e| ≤
      150 * ((natGap d d' : ℝ) + natGap e e') / (ρ : ℝ) := by
  have h₁ := abs_fourierPotential_first_sub_le hρ hfirst
  have h₂ := abs_fourierPotential_second_sub_le hρ hsecond
  calc
    |fourierPotential d' e' - fourierPotential d e| =
        |(fourierPotential d' e' - fourierPotential d' e) +
          (fourierPotential d' e - fourierPotential d e)| := by ring_nf
    _ ≤ |fourierPotential d' e' - fourierPotential d' e| +
        |fourierPotential d' e - fourierPotential d e| := abs_add_le _ _
    _ ≤ 150 * (natGap e e' : ℝ) / (ρ : ℝ) +
        150 * (natGap d d' : ℝ) / (ρ : ℝ) := add_le_add h₂ h₁
    _ = 150 * ((natGap d d' : ℝ) + natGap e e') / (ρ : ℝ) := by ring

/-- Intrinsic form of the gradient estimate: if the total diagonal
displacement `L` is smaller than the starting radius `R`, the whole monotone
path stays outside radius `R-L`. -/
theorem abs_fourierPotential_sub_le_radius_sub_gap {d e d' e' : ℕ}
    (hgap : natGap d d' + natGap e e' < max d e) :
    |fourierPotential d' e' - fourierPotential d e| ≤
      150 * ((natGap d d' : ℝ) + natGap e e') /
        (↑(max d e - (natGap d d' + natGap e e')) : ℝ) := by
  let L := natGap d d' + natGap e e'
  let R := max d e
  let ρ := R - L
  have hρ : 0 < ρ := by dsimp [ρ, R, L]; omega
  have hfirst : ρ ≤ max (min d d') e := by
    have h := radius_le_first_floor_add_gap d d' e
    dsimp [ρ, R, L]
    omega
  have hsecond : ρ ≤ max d' (min e e') := by
    have h := radius_le_second_floor_add_gaps d d' e e'
    dsimp [ρ, R, L]
    omega
  simpa only [ρ, R, L] using abs_fourierPotential_sub_le hρ hfirst hsecond

/-- The two-coordinate estimate transported to even-parity lattice points. -/
theorem abs_planarPotentialKernel_sub_le_of_even {x y : Point} {ρ : ℕ}
    (hx : Even (x.1 + x.2)) (hy : Even (y.1 + y.2))
    (hρ : 0 < ρ)
    (hfirst : ρ ≤ max (min (firstDiagonalOffset x) (firstDiagonalOffset y))
      (secondDiagonalOffset x))
    (hsecond : ρ ≤ max (firstDiagonalOffset y)
      (min (secondDiagonalOffset x) (secondDiagonalOffset y))) :
    |planarPotentialKernel y - planarPotentialKernel x| ≤
      150 * ((natGap (firstDiagonalOffset x) (firstDiagonalOffset y) : ℝ) +
        natGap (secondDiagonalOffset x) (secondDiagonalOffset y)) / (ρ : ℝ) := by
  rw [planarPotentialKernel_eq_diagonalPotential_of_even hx,
    planarPotentialKernel_eq_diagonalPotential_of_even hy,
    diagonalPotential_eq_fourierPotential,
    diagonalPotential_eq_fourierPotential]
  exact abs_fourierPotential_sub_le hρ hfirst hsecond

/-- Intrinsic even-parity lattice version, with denominator equal to the
starting diagonal radius minus the diagonal-coordinate displacement. -/
theorem abs_planarPotentialKernel_sub_le_radius_sub_gap_of_even
    {x y : Point}
    (hx : Even (x.1 + x.2)) (hy : Even (y.1 + y.2))
    (hgap : natGap (firstDiagonalOffset x) (firstDiagonalOffset y) +
        natGap (secondDiagonalOffset x) (secondDiagonalOffset y) <
      max (firstDiagonalOffset x) (secondDiagonalOffset x)) :
    |planarPotentialKernel y - planarPotentialKernel x| ≤
      150 * ((natGap (firstDiagonalOffset x) (firstDiagonalOffset y) : ℝ) +
          natGap (secondDiagonalOffset x) (secondDiagonalOffset y)) /
        (↑(max (firstDiagonalOffset x) (secondDiagonalOffset x) -
          (natGap (firstDiagonalOffset x) (firstDiagonalOffset y) +
            natGap (secondDiagonalOffset x) (secondDiagonalOffset y))) : ℝ) := by
  rw [planarPotentialKernel_eq_diagonalPotential_of_even hx,
    planarPotentialKernel_eq_diagonalPotential_of_even hy,
    diagonalPotential_eq_fourierPotential,
    diagonalPotential_eq_fourierPotential]
  exact abs_fourierPotential_sub_le_radius_sub_gap hgap

/-- Odd-to-even local bridge.  An odd point is the average of its four even
neighbors.  The hypotheses are purely finite diagonal-coordinate geometry:
all four comparisons stay beyond radius `ρ`, and each has total diagonal gap
at most two. -/
theorem abs_planarPotentialKernel_odd_sub_neighbor_le
    {x : Point} (hx : ¬Even (x.1 + x.2)) (d₀ : Direction) {ρ : ℕ}
    (hρ : 0 < ρ)
    (hfirst : ∀ d : Direction,
      ρ ≤ max
        (min (firstDiagonalOffset (x - directionVector d₀))
          (firstDiagonalOffset (x - directionVector d)))
        (secondDiagonalOffset (x - directionVector d₀)))
    (hsecond : ∀ d : Direction,
      ρ ≤ max (firstDiagonalOffset (x - directionVector d))
        (min (secondDiagonalOffset (x - directionVector d₀))
          (secondDiagonalOffset (x - directionVector d))))
    (hgap : ∀ d : Direction,
      natGap (firstDiagonalOffset (x - directionVector d₀))
          (firstDiagonalOffset (x - directionVector d)) +
        natGap (secondDiagonalOffset (x - directionVector d₀))
          (secondDiagonalOffset (x - directionVector d)) ≤ 2) :
    |planarPotentialKernel x -
        planarPotentialKernel (x - directionVector d₀)| ≤
      300 / (ρ : ℝ) := by
  let y := x - directionVector d₀
  have hy : Even (y.1 + y.2) := neighbor_even_of_not_even hx d₀
  have hz (d : Direction) : Even
      ((x - directionVector d).1 + (x - directionVector d).2) :=
    neighbor_even_of_not_even hx d
  rw [planarPotentialKernel_eq_neighbor_average_of_not_even hx]
  have hrewrite :
      (1 / 4 : ℝ) * ∑ d : Direction,
          planarPotentialKernel (x - directionVector d) - planarPotentialKernel y =
        (1 / 4 : ℝ) * ∑ d : Direction,
          (planarPotentialKernel (x - directionVector d) - planarPotentialKernel y) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  change |(1 / 4 : ℝ) * ∑ d : Direction,
      planarPotentialKernel (x - directionVector d) - planarPotentialKernel y| ≤ _
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  calc
    (1 / 4 : ℝ) *
        |∑ d : Direction,
          (planarPotentialKernel (x - directionVector d) - planarPotentialKernel y)| ≤
        (1 / 4 : ℝ) * ∑ d : Direction,
          |planarPotentialKernel (x - directionVector d) - planarPotentialKernel y| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / 4 : ℝ) * ∑ _d : Direction, (300 / (ρ : ℝ)) := by
      gcongr with d
      have hd := abs_planarPotentialKernel_sub_le_of_even hy (hz d) hρ
        (hfirst d) (hsecond d)
      calc
        |planarPotentialKernel (x - directionVector d) - planarPotentialKernel y| ≤
            150 *
                ((natGap (firstDiagonalOffset y)
                      (firstDiagonalOffset (x - directionVector d)) : ℝ) +
                  natGap (secondDiagonalOffset y)
                    (secondDiagonalOffset (x - directionVector d))) /
              (ρ : ℝ) := hd
        _ ≤ 300 / (ρ : ℝ) := by
          have hg : ((natGap (firstDiagonalOffset y)
                    (firstDiagonalOffset (x - directionVector d)) : ℕ) : ℝ) +
                natGap (secondDiagonalOffset y)
                  (secondDiagonalOffset (x - directionVector d)) ≤ 2 := by
            exact_mod_cast hgap d
          have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρ
          rw [div_le_div_iff₀ hρR hρR]
          nlinarith
    _ = 300 / (ρ : ℝ) := by simp

/-- Fully geometric odd-to-even neighbor estimate.  Away from the two-step
core, no auxiliary floor hypotheses remain: every other even neighbor is at
diagonal distance at most two, hence the common radius floor is `R-2`. -/
theorem abs_planarPotentialKernel_odd_sub_neighbor_le_radius
    {x : Point} (hx : ¬Even (x.1 + x.2)) (d₀ : Direction)
    (hR : 2 < max
      (firstDiagonalOffset (x - directionVector d₀))
      (secondDiagonalOffset (x - directionVector d₀))) :
    |planarPotentialKernel x -
        planarPotentialKernel (x - directionVector d₀)| ≤
      300 / (↑(max
        (firstDiagonalOffset (x - directionVector d₀))
        (secondDiagonalOffset (x - directionVector d₀)) - 2) : ℝ) := by
  let y := x - directionVector d₀
  let R := max (firstDiagonalOffset y) (secondDiagonalOffset y)
  have hρ : 0 < R - 2 := by
    apply Nat.sub_pos_of_lt
    simpa only [R, y] using hR
  apply abs_planarPotentialKernel_odd_sub_neighbor_le hx d₀ hρ
  · intro d
    have hr := radius_le_first_floor_add_gap
      (firstDiagonalOffset y)
      (firstDiagonalOffset (x - directionVector d))
      (secondDiagonalOffset y)
    have hg := neighbor_diagonalOffset_gap_le_two x d₀ d
    have hg' : natGap (firstDiagonalOffset y)
          (firstDiagonalOffset (x - directionVector d)) +
        natGap (secondDiagonalOffset y)
          (secondDiagonalOffset (x - directionVector d)) ≤ 2 := by
      simpa only [y] using hg
    change R - 2 ≤ max
      (min (firstDiagonalOffset y)
        (firstDiagonalOffset (x - directionVector d)))
      (secondDiagonalOffset y)
    dsimp [R]
    omega
  · intro d
    have hr := radius_le_second_floor_add_gaps
      (firstDiagonalOffset y)
      (firstDiagonalOffset (x - directionVector d))
      (secondDiagonalOffset y)
      (secondDiagonalOffset (x - directionVector d))
    have hg := neighbor_diagonalOffset_gap_le_two x d₀ d
    have hg' : natGap (firstDiagonalOffset y)
          (firstDiagonalOffset (x - directionVector d)) +
        natGap (secondDiagonalOffset y)
          (secondDiagonalOffset (x - directionVector d)) ≤ 2 := by
      simpa only [y] using hg
    change R - 2 ≤ max (firstDiagonalOffset (x - directionVector d))
      (min (secondDiagonalOffset y)
        (secondDiagonalOffset (x - directionVector d)))
    dsimp [R]
    omega
  · exact neighbor_diagonalOffset_gap_le_two x d₀

lemma add_direction_not_even_of_even {x : Point}
    (hx : Even (x.1 + x.2)) (d : Direction) :
    ¬Even ((x + directionVector d).1 + (x + directionVector d).2) := by
  have hdodd : Odd ((directionVector d).1 + (directionVector d).2) := by
    fin_cases d <;> norm_num [directionVector]
  have hodd := hx.add_odd hdodd
  rw [Int.not_even_iff_odd]
  change Odd ((x.1 + (directionVector d).1) +
    (x.2 + (directionVector d).2))
  convert hodd using 1
  ring

/-- Local gradient across an arbitrary nearest-neighbor edge, oriented from
its even endpoint.  The bound is `O(1/R)` with an explicit constant and no
remaining analytic or geometric assumptions. -/
theorem abs_planarPotentialKernel_add_direction_sub_le_radius_of_even
    {x : Point} (hx : Even (x.1 + x.2)) (d : Direction)
    (hR : 2 < max (firstDiagonalOffset x) (secondDiagonalOffset x)) :
    |planarPotentialKernel (x + directionVector d) -
        planarPotentialKernel x| ≤
      300 / (↑(max (firstDiagonalOffset x) (secondDiagonalOffset x) - 2) : ℝ) := by
  let z := x + directionVector d
  have hz : ¬Even (z.1 + z.2) := by
    exact add_direction_not_even_of_even hx d
  have hback : z - directionVector d = x := by
    ext <;> simp [z]
  have h := abs_planarPotentialKernel_odd_sub_neighbor_le_radius hz d
    (by simpa only [hback] using hR)
  rw [hback] at h
  simpa [abs_sub_comm] using h

end PotentialGradient
end Erdos1165
