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

import ErdosProblems.Erdos1165.PlanarLocalCLT
import ErdosProblems.Erdos1165.PotentialFourierIntegral
import ErdosProblems.Erdos1165.PotentialRadialSums

/-!
# Radial comparison of the Fourier masses

This file isolates the cancellation which makes the planar potential kernel
asymptotically radial.  A product of two centered binomial masses has Gaussian
main term

`exp (-(d^2+e^2)/n) / (pi*n)`.

Consequently the main terms for two pairs with the same squared radius cancel.
The lemmas below give a completely explicit pointwise bound for the remaining
local-CLT errors.  They are stated in a slightly more flexible form, suitable
also for comparing squared radii which differ by `O(rho)`.
-/

open Real
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialRadialMass

open BinomialGaussian PlanarLocalCLT PotentialKernel PotentialFourierIntegral
  PotentialRadialSums

/-- Squared radius in the independent diagonal coordinates. -/
def radiusSq (d e : ℕ) : ℕ := d ^ 2 + e ^ 2

/-- Gaussian main term for the product Fourier mass.  The `n = 0` value is
set to zero; all approximation lemmas below assume `n > 0`. -/
noncomputable def radialGaussianMass (Q n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.exp (-(Q : ℝ) / n) / (Real.pi * n)

/-- Sum of the two one-dimensional logarithmic local-CLT errors. -/
noncomputable def productGaussianError (n d e : ℕ) : ℝ :=
  coordinateGaussianError n d + coordinateGaussianError n e

/-- Product mass after removal of its radial Gaussian main term. -/
noncomputable def normalizedFourierProductMass (n d e : ℕ) : ℝ :=
  fourierProductMass n d e * (Real.pi * n) *
    Real.exp ((radiusSq d e : ℕ) / n)

lemma productGaussianError_nonneg {n d e : ℕ}
    (hd : d < n) (he : e < n) :
    0 ≤ productGaussianError n d e := by
  unfold productGaussianError
  exact add_nonneg (coordinateGaussianError_nonneg hd)
    (coordinateGaussianError_nonneg he)

/-- The product version of the explicit binomial local CLT. -/
theorem normalizedFourierProductMass_bounds {n d e : ℕ}
    (hn : 0 < n) (hd : d < n) (he : e < n)
    (hmoderateD : 2 * d ≤ n) (hmoderateE : 2 * e ≤ n) :
    Real.exp (-productGaussianError n d e) ≤
        normalizedFourierProductMass n d e ∧
      normalizedFourierProductMass n d e ≤
        Real.exp (productGaussianError n d e) := by
  have hdg := evenSymmetricMass_gaussian_bounds hn hd hmoderateD
  have heg := evenSymmetricMass_gaussian_bounds hn he hmoderateE
  dsimp only at hdg heg
  have hsqrt : Real.sqrt (Real.pi * n) ^ 2 = Real.pi * n :=
    Real.sq_sqrt (by positivity)
  have hexp :
      Real.exp ((radiusSq d e : ℕ) / (n : ℝ)) =
        Real.exp ((d : ℝ) ^ 2 / n) * Real.exp ((e : ℝ) ^ 2 / n) := by
    rw [← Real.exp_add]
    congr 1
    unfold radiusSq
    push_cast
    ring
  unfold normalizedFourierProductMass fourierProductMass productGaussianError
  rw [hexp, ← hsqrt]
  constructor
  · rw [neg_add, Real.exp_add]
    calc
      Real.exp (-coordinateGaussianError n d) *
          Real.exp (-coordinateGaussianError n e) ≤
        (evenSymmetricMass n d * Real.sqrt (Real.pi * n) *
            Real.exp ((d : ℝ) ^ 2 / n)) *
          (evenSymmetricMass n e * Real.sqrt (Real.pi * n) *
            Real.exp ((e : ℝ) ^ 2 / n)) :=
        mul_le_mul hdg.1 heg.1 (Real.exp_pos _).le
          (mul_nonneg
            (mul_nonneg (evenSymmetricMass_pos hd.le).le (Real.sqrt_nonneg _))
            (Real.exp_pos _).le)
      _ = evenSymmetricMass n d * evenSymmetricMass n e *
          Real.sqrt (Real.pi * n) ^ 2 *
            (Real.exp ((d : ℝ) ^ 2 / n) *
              Real.exp ((e : ℝ) ^ 2 / n)) := by ring
  · rw [Real.exp_add]
    calc
      evenSymmetricMass n d * evenSymmetricMass n e *
          Real.sqrt (Real.pi * n) ^ 2 *
            (Real.exp ((d : ℝ) ^ 2 / n) *
              Real.exp ((e : ℝ) ^ 2 / n)) =
        (evenSymmetricMass n d * Real.sqrt (Real.pi * n) *
            Real.exp ((d : ℝ) ^ 2 / n)) *
          (evenSymmetricMass n e * Real.sqrt (Real.pi * n) *
            Real.exp ((e : ℝ) ^ 2 / n)) := by ring
      _ ≤ Real.exp (coordinateGaussianError n d) *
          Real.exp (coordinateGaussianError n e) :=
        mul_le_mul hdg.2 heg.2
          (mul_nonneg
            (mul_nonneg (evenSymmetricMass_pos he.le).le (Real.sqrt_nonneg _))
            (Real.exp_pos _).le)
          (Real.exp_pos _).le

lemma radialGaussianMass_eq {Q n : ℕ} (hn : 0 < n) :
    radialGaussianMass Q n =
      Real.exp (-(Q : ℝ) / n) / (Real.pi * n) := by
  simp [radialGaussianMass, hn.ne']

/-- Exact factorization of the product mass into its Gaussian main term and
the normalized mass. -/
lemma fourierProductMass_eq_radial_mul_normalized {n d e : ℕ} (hn : 0 < n) :
    fourierProductMass n d e =
      radialGaussianMass (radiusSq d e) n *
        normalizedFourierProductMass n d e := by
  rw [radialGaussianMass_eq hn]
  unfold normalizedFourierProductMass
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : Real.pi * (n : ℝ) ≠ 0 :=
    mul_ne_zero (ne_of_gt Real.pi_pos) hnR.ne'
  calc
    fourierProductMass n d e = fourierProductMass n d e * 1 := by ring
    _ = fourierProductMass n d e *
        (Real.exp (-(radiusSq d e : ℝ) / n) *
          Real.exp ((radiusSq d e : ℝ) / n)) := by
      rw [← Real.exp_add]
      congr 1
      rw [show -(radiusSq d e : ℝ) / n +
        (radiusSq d e : ℝ) / n = 0 by ring, Real.exp_zero]
    _ = (Real.exp (-(radiusSq d e : ℝ) / n) /
          (Real.pi * n)) *
        (fourierProductMass n d e * (Real.pi * n) *
          Real.exp ((radiusSq d e : ℝ) / n)) := by
      field_simp

/-- A nonnegative number trapped between `exp (-E)` and `exp E` differs from
one by at most `E exp E`. -/
lemma abs_sub_one_le_mul_exp {z E : ℝ} (hE : 0 ≤ E)
    (hlower : Real.exp (-E) ≤ z) (hupper : z ≤ Real.exp E) :
    |z - 1| ≤ E * Real.exp E := by
  have hExpOne : 1 ≤ Real.exp E := Real.one_le_exp hE
  have hupper' : z - 1 ≤ E * Real.exp E := by
    calc
      z - 1 ≤ Real.exp E - 1 := sub_le_sub_right hupper 1
      _ = Real.exp E * (1 - Real.exp (-E)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ Real.exp E * E := by
        gcongr
        linarith [Real.one_sub_le_exp_neg E]
      _ = E * Real.exp E := by ring
  have hlower' : -(E * Real.exp E) ≤ z - 1 := by
    have honeSub : 1 - Real.exp (-E) ≤ E := by
      linarith [Real.one_sub_le_exp_neg E]
    have hEexp : E ≤ E * Real.exp E := by
      nlinarith
    linarith
  exact (abs_le).2 ⟨hlower', hupper'⟩

/-- Pointwise local-CLT error for a product mass. -/
theorem abs_fourierProductMass_sub_radialGaussianMass_le
    {n d e : ℕ} (hn : 0 < n) (hd : d < n) (he : e < n)
    (hmoderateD : 2 * d ≤ n) (hmoderateE : 2 * e ≤ n) :
    |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| ≤
      radialGaussianMass (radiusSq d e) n *
        (productGaussianError n d e *
          Real.exp (productGaussianError n d e)) := by
  have hbounds := normalizedFourierProductMass_bounds hn hd he
    hmoderateD hmoderateE
  have hE := productGaussianError_nonneg hd he
  have hnorm := abs_sub_one_le_mul_exp hE hbounds.1 hbounds.2
  rw [fourierProductMass_eq_radial_mul_normalized hn]
  have hg : 0 ≤ radialGaussianMass (radiusSq d e) n := by
    rw [radialGaussianMass_eq hn]
    positivity
  rw [show radialGaussianMass (radiusSq d e) n *
      normalizedFourierProductMass n d e -
        radialGaussianMass (radiusSq d e) n =
      radialGaussianMass (radiusSq d e) n *
        (normalizedFourierProductMass n d e - 1) by ring,
    abs_mul, abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left hnorm hg

/-- Explicit algebraic envelope for the product log-error. -/
theorem productGaussianError_le_radius {n d e ρ : ℕ}
    (hn : 0 < n) (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hmoderateD : 2 * d ≤ n) (hmoderateE : 2 * e ≤ n) :
    productGaussianError n d e ≤
      16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
        (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ)) := by
  have hdlt : d < n := by omega
  have helt : e < n := by omega
  have hdn : (n : ℝ) - d ≥ n / 2 := by
    have h : (2 : ℝ) * d ≤ n := by exact_mod_cast hmoderateD
    linarith
  have hen : (n : ℝ) - e ≥ n / 2 := by
    have h : (2 : ℝ) * e ≤ n := by exact_mod_cast hmoderateE
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdsub : (0 : ℝ) < n - d := sub_pos.mpr (by exact_mod_cast hdlt)
  have hesum : (0 : ℝ) < n - e := sub_pos.mpr (by exact_mod_cast helt)
  have hdrecip : (1 : ℝ) / (6 * (n - d)) ≤ 1 / (3 * n) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * (n - d))
      (by positivity : (0 : ℝ) < 3 * n)]
    nlinarith
  have herecip : (1 : ℝ) / (6 * (n - e)) ≤ 1 / (3 * n) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * (n - e))
      (by positivity : (0 : ℝ) < 3 * n)]
    nlinarith
  have hdR : (d : ℝ) ≤ 2 * ρ := by exact_mod_cast hdρ
  have heR : (e : ℝ) ≤ 2 * ρ := by exact_mod_cast heρ
  have hdcube : (d : ℝ) ^ 3 ≤ 2 * (ρ : ℝ) * d ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sub_nonneg.mpr hdR)]
  have hecube : (e : ℝ) ^ 3 ≤ 2 * (ρ : ℝ) * e ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (e : ℝ)) (sub_nonneg.mpr heR)]
  rw [productGaussianError, coordinateGaussianError_eq hn,
    coordinateGaussianError_eq hn]
  unfold radiusSq
  push_cast
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hcubic :
      8 * (d : ℝ) ^ 3 / n ^ 2 + 8 * (e : ℝ) ^ 3 / n ^ 2 ≤
        16 * (ρ : ℝ) * ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2 := by
    rw [← add_div, div_le_div_iff₀ hn2 hn2]
    nlinarith
  calc
    8 * (d : ℝ) ^ 3 / n ^ 2 + (d : ℝ) ^ 2 / n ^ 2 +
          1 / (6 * (n - d)) +
        (8 * (e : ℝ) ^ 3 / n ^ 2 + (e : ℝ) ^ 2 / n ^ 2 +
          1 / (6 * (n - e))) =
      (8 * (d : ℝ) ^ 3 / n ^ 2 + 8 * (e : ℝ) ^ 3 / n ^ 2) +
        ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2 +
        1 / (6 * (n - d)) + 1 / (6 * (n - e)) := by ring
    _ ≤ 16 * (ρ : ℝ) * ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2 +
        ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2 + 2 / (3 * n) := by
      have hrecip := add_le_add hdrecip herecip
      calc
        (8 * (d : ℝ) ^ 3 / n ^ 2 + 8 * (e : ℝ) ^ 3 / n ^ 2) +
            ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2 +
            1 / (6 * (n - d)) + 1 / (6 * (n - e)) =
          ((8 * (d : ℝ) ^ 3 / n ^ 2 + 8 * (e : ℝ) ^ 3 / n ^ 2) +
            ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2) +
              (1 / (6 * (n - d)) + 1 / (6 * (n - e))) := by ring
        _ ≤
          16 * (ρ : ℝ) * ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2 +
            ((d : ℝ) ^ 2 + e ^ 2) / n ^ 2 +
            (1 / (3 * n) + 1 / (3 * n)) := by
          exact add_le_add (add_le_add hcubic le_rfl) hrecip
        _ = _ := by ring

/-- At times at least `64 rho`, the logarithmic error consumes at most half
of the radial Gaussian exponent. -/
theorem productGaussianError_le_half_radius_exponent
    {n d e ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hn : 64 * ρ ≤ n) :
    productGaussianError n d e ≤
      (radiusSq d e : ℝ) / (2 * (n : ℝ)) := by
  have hn0 : 0 < n := by omega
  have hdmod : 2 * d ≤ n := (Nat.mul_le_mul_left 2 hdρ).trans (by omega)
  have hemod : 2 * e ≤ n := (Nat.mul_le_mul_left 2 heρ).trans (by omega)
  have hraw := productGaussianError_le_radius hn0 hdρ heρ hdmod hemod
  have hρR : (0 : ℝ) < ρ := by positivity
  have hnR : (64 : ℝ) * ρ ≤ n := by exact_mod_cast hn
  have hQloNat : ρ ^ 2 ≤ radiusSq d e := by
    unfold radiusSq
    rcases max_cases d e with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_right _ _)
    · rw [h] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_left _ _)
  have hQlo : (ρ : ℝ) ^ 2 ≤ (radiusSq d e : ℕ) := by exact_mod_cast hQloNat
  have hnPos : (0 : ℝ) < n := by positivity
  have hQpos : (0 : ℝ) < (radiusSq d e : ℕ) :=
    lt_of_lt_of_le (sq_pos_of_pos hρR) hQlo
  calc
    productGaussianError n d e ≤
        16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ)) := hraw
    _ ≤ (radiusSq d e : ℝ) / (2 * (n : ℝ)) := by
      rw [show (radiusSq d e : ℝ) / (2 * (n : ℝ)) =
        (radiusSq d e : ℝ) / n * (1 / 2) by ring]
      have hfirst : 16 * (ρ : ℝ) * (radiusSq d e : ℝ) / n ^ 2 ≤
          (radiusSq d e : ℝ) / n * (1 / 4) := by
        have hc : 16 * (ρ : ℝ) / n ≤ (1 : ℝ) / 4 := by
          rw [div_le_iff₀ hnPos]
          nlinarith
        calc
          16 * (ρ : ℝ) * (radiusSq d e : ℝ) / n ^ 2 =
              (radiusSq d e : ℝ) / n * (16 * ρ / n) := by ring
          _ ≤ (radiusSq d e : ℝ) / n * (1 / 4) := by gcongr
      have hsecond : (radiusSq d e : ℝ) / n ^ 2 ≤
          (radiusSq d e : ℝ) / n * (1 / 64) := by
        have hρone : (1 : ℝ) ≤ ρ := by exact_mod_cast (show 1 ≤ ρ by omega)
        have hn64 : (64 : ℝ) ≤ n := by nlinarith
        have hc : (1 : ℝ) / n ≤ 1 / 64 := by
          rw [div_le_div_iff₀ hnPos (by norm_num : (0 : ℝ) < 64)]
          simpa using hn64
        calc
          (radiusSq d e : ℝ) / n ^ 2 =
              (radiusSq d e : ℝ) / n * (1 / n) := by ring
          _ ≤ (radiusSq d e : ℝ) / n * (1 / 64) := by gcongr
      have hthird : 2 / (3 * (n : ℝ)) ≤
          (radiusSq d e : ℝ) / n * (1 / 6) := by
        have hρtwo : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
        have hQfour : (4 : ℝ) ≤ (radiusSq d e : ℕ) := by nlinarith
        have hconst : (2 : ℝ) / 3 ≤ (radiusSq d e : ℝ) / 6 := by
          nlinarith
        calc
          2 / (3 * (n : ℝ)) = (1 / n) * (2 / 3) := by ring
          _ ≤ (1 / n) * ((radiusSq d e : ℝ) / 6) := by gcongr
          _ = (radiusSq d e : ℝ) / n * (1 / 6) := by ring
      calc
        16 * (ρ : ℝ) * (radiusSq d e : ℝ) / n ^ 2 +
            (radiusSq d e : ℝ) / n ^ 2 + 2 / (3 * n) ≤
          (radiusSq d e : ℝ) / n * (1 / 4) +
            (radiusSq d e : ℝ) / n * (1 / 64) +
              (radiusSq d e : ℝ) / n * (1 / 6) :=
          add_le_add (add_le_add hfirst hsecond) hthird
        _ ≤ (radiusSq d e : ℝ) / n * (1 / 2) := by
          have : 0 ≤ (radiusSq d e : ℝ) / n := by positivity
          nlinarith

/-- Late-time local-CLT error with its Gaussian decay retained. -/
theorem abs_fourierProductMass_sub_radialGaussianMass_late_le
    {n d e ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hn : 64 * ρ ≤ n) :
    |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| ≤
      Real.exp (-(radiusSq d e : ℝ) / (2 * n)) /
          (Real.pi * n) *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ))) := by
  have hn0 : 0 < n := by omega
  have hdmod : 2 * d ≤ n := (Nat.mul_le_mul_left 2 hdρ).trans (by omega)
  have hemod : 2 * e ≤ n := (Nat.mul_le_mul_left 2 heρ).trans (by omega)
  have hdlt : d < n := by omega
  have helt : e < n := by omega
  have hbase := abs_fourierProductMass_sub_radialGaussianMass_le hn0 hdlt helt
    hdmod hemod
  have hE := productGaussianError_nonneg hdlt helt
  have hEbound := productGaussianError_le_radius hn0 hdρ heρ hdmod hemod
  have hEhalf := productGaussianError_le_half_radius_exponent hρ hdρ heρ hradius hn
  have hEhalf' : productGaussianError n d e ≤
      ((radiusSq d e : ℝ) / n) / 2 := by
    convert hEhalf using 1
    ring
  have hbase' :
      |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| ≤
        (Real.exp (-(radiusSq d e : ℝ) / n) / (Real.pi * n)) *
          (productGaussianError n d e * Real.exp (productGaussianError n d e)) := by
    simpa [radialGaussianMass_eq hn0] using hbase
  calc
    |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| ≤
      (Real.exp (-(radiusSq d e : ℝ) / n) / (Real.pi * n)) *
        (productGaussianError n d e * Real.exp (productGaussianError n d e)) := hbase'
    _ = Real.exp (-(radiusSq d e : ℝ) / n +
          productGaussianError n d e) / (Real.pi * n) *
        productGaussianError n d e := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (-(radiusSq d e : ℝ) / (2 * n)) /
          (Real.pi * n) * productGaussianError n d e := by
      gcongr
      rw [show -(radiusSq d e : ℝ) / n =
          -((radiusSq d e : ℝ) / n) by ring,
        show -(radiusSq d e : ℝ) / (2 * n) =
        -(((radiusSq d e : ℝ) / n) / 2) by ring]
      linarith
    _ ≤ Real.exp (-(radiusSq d e : ℝ) / (2 * n)) /
          (Real.pi * n) *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ))) := by
      gcongr

/-- At equal squared radius the two Gaussian main terms cancel exactly. -/
theorem abs_fourierProductMass_sub_le_of_radiusSq_eq_late
    {n d e d' e' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hdρ' : d' ≤ 2 * ρ) (heρ' : e' ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hQ : radiusSq d e = radiusSq d' e') (hn : 64 * ρ ≤ n) :
    |fourierProductMass n d e - fourierProductMass n d' e'| ≤
      2 * (Real.exp (-(radiusSq d e : ℝ) / (2 * n)) /
          (Real.pi * n) *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ)))) := by
  have h₁ := abs_fourierProductMass_sub_radialGaussianMass_late_le
    hρ hdρ heρ hradius hn
  have h₂ := abs_fourierProductMass_sub_radialGaussianMass_late_le
    hρ hdρ' heρ' hradius' hn
  rw [← hQ] at h₂
  calc
    |fourierProductMass n d e - fourierProductMass n d' e'| =
        |(fourierProductMass n d e - radialGaussianMass (radiusSq d e) n) -
          (fourierProductMass n d' e' - radialGaussianMass (radiusSq d e) n)| := by
      ring_nf
    _ ≤ |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| +
        |fourierProductMass n d' e' - radialGaussianMass (radiusSq d e) n| :=
      abs_sub _ _
    _ ≤ _ := by linarith

lemma squareGaussianWeight_pred {Q n : ℕ} (hn : 0 < n) :
    squareGaussianWeight Q (n - 1) =
      Real.exp (-(Q : ℝ) / (2 * n)) / (n : ℝ) ^ 2 := by
  unfold squareGaussianWeight
  have hnat : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hreal : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hnat
  rw [hreal]

lemma cubeGaussianWeight_pred {Q n : ℕ} (hn : 0 < n) :
    cubeGaussianWeight Q (n - 1) =
      Real.exp (-(Q : ℝ) / (2 * n)) / (n : ℝ) ^ 3 := by
  unfold cubeGaussianWeight
  have hnat : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hreal : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hnat
  rw [hreal]

/-- The equal-radius late-time comparison expressed directly in the two
summable Gaussian weights. -/
theorem abs_fourierProductMass_sub_le_of_radiusSq_eq_late_weights
    {n d e d' e' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hdρ' : d' ≤ 2 * ρ) (heρ' : e' ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hQ : radiusSq d e = radiusSq d' e') (hn : 64 * ρ ≤ n) :
    |fourierProductMass n d e - fourierProductMass n d' e'| ≤
      (32 * (ρ : ℝ) * (radiusSq d e : ℝ) +
          2 * (radiusSq d e : ℝ)) *
        cubeGaussianWeight (radiusSq d e) (n - 1) +
      (4 / 3 : ℝ) * squareGaussianWeight (radiusSq d e) (n - 1) := by
  have hn0 : 0 < n := by omega
  have hraw := abs_fourierProductMass_sub_le_of_radiusSq_eq_late hρ hdρ heρ
    hdρ' heρ' hradius hradius' hQ hn
  have hpi : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hden : (n : ℝ) ≤ Real.pi * n := by nlinarith
  have hexp : 0 ≤ Real.exp (-(radiusSq d e : ℝ) / (2 * n)) :=
    (Real.exp_pos _).le
  have hprefactor :
      Real.exp (-(radiusSq d e : ℝ) / (2 * n)) / (Real.pi * n) ≤
        Real.exp (-(radiusSq d e : ℝ) / (2 * n)) / n :=
    div_le_div_of_nonneg_left hexp hnR hden
  have henvelope : 0 ≤
      16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
        (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ)) := by
    positivity
  calc
    |fourierProductMass n d e - fourierProductMass n d' e'| ≤
      2 * (Real.exp (-(radiusSq d e : ℝ) / (2 * n)) /
          (Real.pi * n) *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ)))) := hraw
    _ ≤ 2 * (Real.exp (-(radiusSq d e : ℝ) / (2 * n)) / n *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ)))) := by
      gcongr
    _ = (32 * (ρ : ℝ) * (radiusSq d e : ℝ) +
          2 * (radiusSq d e : ℝ)) *
        cubeGaussianWeight (radiusSq d e) (n - 1) +
      (4 / 3 : ℝ) * squareGaussianWeight (radiusSq d e) (n - 1) := by
      rw [squareGaussianWeight_pred hn0, cubeGaussianWeight_pred hn0]
      ring

lemma fourierProductMass_nonneg (n d e : ℕ) :
    0 ≤ fourierProductMass n d e := by
  unfold fourierProductMass evenSymmetricMass symBinomialMass
  positivity

private lemma exp_neg_le_six_div_cube {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 6 / x ^ 3 := by
  have hpow : x ^ 3 / 6 ≤ Real.exp x := by
    have h := Real.pow_div_factorial_le_exp x hx.le 3
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos x) (pow_pos hx 3)).2
  nlinarith

/-- Before the linear cutoff `64 rho`, any Fourier mass whose diagonal
radius is at least `rho` is already polynomially tiny. -/
theorem fourierProductMass_early_le {n d e ρ : ℕ}
    (hρ : 2 ≤ ρ) (hradius : ρ ≤ max d e) (hn : n < 64 * ρ) :
    fourierProductMass n d e ≤
      12582912 / (ρ : ℝ) ^ 3 := by
  have hρR : (0 : ℝ) < ρ := by positivity
  have hρmax : (ρ : ℝ) ≤ max d e := by exact_mod_cast hradius
  have hexpPoly : Real.exp (-(ρ : ℝ) / 128) ≤
      12582912 / (ρ : ℝ) ^ 3 := by
    have h := exp_neg_le_six_div_cube
      (show (0 : ℝ) < (ρ : ℝ) / 128 by positivity)
    calc
      Real.exp (-(ρ : ℝ) / 128) = Real.exp (-((ρ : ℝ) / 128)) := by ring_nf
      _ ≤ 6 / ((ρ : ℝ) / 128) ^ 3 := h
      _ = 12582912 / (ρ : ℝ) ^ 3 := by field_simp; ring
  by_cases hsupport : max d e ≤ n
  · have hn0 : 0 < n := lt_of_lt_of_le (by omega : 0 < ρ) (hradius.trans hsupport)
    have hd : d ≤ n := (le_max_left d e).trans hsupport
    have he : e ≤ n := (le_max_right d e).trans hsupport
    have hgauss := fourierProductMass_gaussian_le hn0 hd he
    have hreturn : planarReturnProbability n ≤ 1 := by
      calc
        planarReturnProbability n ≤ 1 / (n + 1 : ℝ) :=
          planarReturnProbability_upper_bound n
        _ ≤ 1 := by
          have hone : (1 : ℝ) ≤ n + 1 := by
            exact le_add_of_nonneg_left (Nat.cast_nonneg n)
          simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hone
    have hnR : (n : ℝ) ≤ 64 * ρ := by
      exact_mod_cast (Nat.le_of_lt hn)
    have hfrac : (ρ : ℝ) / 128 ≤
        ((max d e : ℕ) : ℝ) ^ 2 / (2 * n) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 128)
        (by positivity : (0 : ℝ) < 2 * n)]
      nlinarith [sq_le_sq₀ (by positivity : (0 : ℝ) ≤ ρ)
        (by positivity : (0 : ℝ) ≤ (max d e : ℕ)) |>.2 hρmax]
    have hexp : Real.exp (-((max d e : ℕ) : ℝ) ^ 2 / (2 * n)) ≤
        Real.exp (-(ρ : ℝ) / 128) := by
      apply Real.exp_le_exp.mpr
      rw [show -((max d e : ℕ) : ℝ) ^ 2 / (2 * n) =
        -(((max d e : ℕ) : ℝ) ^ 2 / (2 * n)) by ring,
        show -(ρ : ℝ) / 128 = -((ρ : ℝ) / 128) by ring]
      exact neg_le_neg hfrac
    calc
      fourierProductMass n d e ≤ planarReturnProbability n *
          Real.exp (-((max d e : ℕ) : ℝ) ^ 2 / (2 * n)) := hgauss
      _ ≤ 1 * Real.exp (-((max d e : ℕ) : ℝ) ^ 2 / (2 * n)) :=
        mul_le_mul_of_nonneg_right hreturn (Real.exp_pos _).le
      _ ≤ 1 * Real.exp (-(ρ : ℝ) / 128) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ 12582912 / (ρ : ℝ) ^ 3 := by simpa using hexpPoly
  · have hz := fourierProductMass_eq_zero_of_lt_max (Nat.lt_of_not_ge hsupport)
    rw [hz]
    positivity

/-- Equal-radius Fourier masses have a uniform early-time difference bound. -/
theorem abs_fourierProductMass_sub_le_of_radiusSq_eq_early
    {n d e d' e' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hn : n < 64 * ρ) :
    |fourierProductMass n d e - fourierProductMass n d' e'| ≤
      25165824 / (ρ : ℝ) ^ 3 := by
  have h₁ := fourierProductMass_early_le hρ hradius hn
  have h₂ := fourierProductMass_early_le hρ hradius' hn
  calc
    |fourierProductMass n d e - fourierProductMass n d' e'| ≤
        fourierProductMass n d e + fourierProductMass n d' e' := by
      simpa only [abs_of_nonneg (fourierProductMass_nonneg n d e),
        abs_of_nonneg (fourierProductMass_nonneg n d' e')] using
          abs_sub (fourierProductMass n d e) (fourierProductMass n d' e')
    _ ≤ 12582912 / (ρ : ℝ) ^ 3 + 12582912 / (ρ : ℝ) ^ 3 :=
      add_le_add h₁ h₂
    _ = 25165824 / (ρ : ℝ) ^ 3 := by ring

/-- Elementary Lipschitz estimate for the radial exponential. -/
lemma abs_exp_neg_sub_exp_neg_le (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)| ≤
      |a - b| * Real.exp (-min a b) := by
  rcases le_total a b with hab | hba
  · have hexp : Real.exp (-b) ≤ Real.exp (-a) :=
      Real.exp_le_exp.mpr (neg_le_neg hab)
    have hgap : 0 ≤ b - a := sub_nonneg.mpr hab
    have hone : 1 - Real.exp (-(b - a)) ≤ b - a := by
      linarith [Real.one_sub_le_exp_neg (b - a)]
    rw [abs_of_nonneg (sub_nonneg.mpr hexp), min_eq_left hab]
    calc
      Real.exp (-a) - Real.exp (-b) =
          Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
        rw [show -b = -a + -(b - a) by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-a) * (b - a) :=
        mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
      _ = |a - b| * Real.exp (-a) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
  · have hexp : Real.exp (-a) ≤ Real.exp (-b) :=
      Real.exp_le_exp.mpr (neg_le_neg hba)
    have hgap : 0 ≤ a - b := sub_nonneg.mpr hba
    have hone : 1 - Real.exp (-(a - b)) ≤ a - b := by
      linarith [Real.one_sub_le_exp_neg (a - b)]
    rw [abs_of_nonpos (sub_nonpos.mpr hexp), min_eq_right hba]
    calc
      -(Real.exp (-a) - Real.exp (-b)) =
          Real.exp (-b) * (1 - Real.exp (-(a - b))) := by
        rw [show -a = -b + -(a - b) by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-b) * (a - b) :=
        mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
      _ = |a - b| * Real.exp (-b) := by
        rw [abs_of_nonneg hgap]
        ring

/-- Lipschitz comparison of two radial Gaussian main terms. -/
theorem abs_radialGaussianMass_sub_le {Q Q' n : ℕ} (hn : 0 < n) :
    |radialGaussianMass Q n - radialGaussianMass Q' n| ≤
      (|(Q : ℝ) - (Q' : ℝ)| / n) *
        (Real.exp (-(min Q Q' : ℕ) / n) / (Real.pi * n)) := by
  rw [radialGaussianMass_eq hn, radialGaussianMass_eq hn,
    ← sub_div, abs_div]
  have hden : 0 < Real.pi * (n : ℝ) := by positivity
  rw [abs_of_pos hden]
  have h := abs_exp_neg_sub_exp_neg_le ((Q : ℝ) / n) ((Q' : ℝ) / n)
  have hmin : min ((Q : ℝ) / n) ((Q' : ℝ) / n) =
      ((min Q Q' : ℕ) : ℝ) / n := by
    rcases le_total Q Q' with hQQ | hQQ
    · rw [min_eq_left hQQ, min_eq_left]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hQQ) (by positivity)
    · rw [min_eq_right hQQ, min_eq_right]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hQQ) (by positivity)
  have hgap : |(Q : ℝ) / n - (Q' : ℝ) / n| =
      |(Q : ℝ) - (Q' : ℝ)| / n := by
    rw [← sub_div, abs_div, abs_of_pos (show (0 : ℝ) < n by positivity)]
  rw [hmin, hgap] at h
  calc
    |Real.exp (-(Q : ℝ) / n) - Real.exp (-(Q' : ℝ) / n)| /
        (Real.pi * n) ≤
      (|(Q : ℝ) - (Q' : ℝ)| / n *
        Real.exp (-((min Q Q' : ℕ) : ℝ) / n)) / (Real.pi * n) := by
      gcongr
      simpa only [neg_div] using h
    _ = (|(Q : ℝ) - (Q' : ℝ)| / n) *
        (Real.exp (-(min Q Q' : ℕ) / n) / (Real.pi * n)) := by ring

/-- Late-time comparison for nearby (not necessarily equal) radii.  The first
and third summands are the two local-CLT errors; the middle summand is the
explicit radial Gaussian Lipschitz error. -/
theorem abs_fourierProductMass_sub_le_late
    {n d e d' e' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hdρ' : d' ≤ 2 * ρ) (heρ' : e' ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hn : 64 * ρ ≤ n) :
    |fourierProductMass n d e - fourierProductMass n d' e'| ≤
      Real.exp (-(radiusSq d e : ℝ) / (2 * n)) /
          (Real.pi * n) *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ))) +
      (|(radiusSq d e : ℝ) - (radiusSq d' e' : ℝ)| / n) *
        (Real.exp (-(min (radiusSq d e) (radiusSq d' e') : ℕ) / n) /
          (Real.pi * n)) +
      Real.exp (-(radiusSq d' e' : ℝ) / (2 * n)) /
          (Real.pi * n) *
        (16 * (ρ : ℝ) * (radiusSq d' e' : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d' e' : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ))) := by
  have hn0 : 0 < n := by omega
  have h₁ := abs_fourierProductMass_sub_radialGaussianMass_late_le
    hρ hdρ heρ hradius hn
  have h₂ := abs_radialGaussianMass_sub_le (Q := radiusSq d e)
    (Q' := radiusSq d' e') hn0
  have h₃ := abs_fourierProductMass_sub_radialGaussianMass_late_le
    hρ hdρ' heρ' hradius' hn
  calc
    |fourierProductMass n d e - fourierProductMass n d' e'| =
        |(fourierProductMass n d e - radialGaussianMass (radiusSq d e) n) +
          (radialGaussianMass (radiusSq d e) n -
            radialGaussianMass (radiusSq d' e') n) +
          (radialGaussianMass (radiusSq d' e') n -
            fourierProductMass n d' e')| := by ring_nf
    _ ≤ |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| +
        |radialGaussianMass (radiusSq d e) n -
          radialGaussianMass (radiusSq d' e') n| +
        |radialGaussianMass (radiusSq d' e') n -
          fourierProductMass n d' e'| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [abs_sub_comm (radialGaussianMass (radiusSq d' e') n)]
      exact add_le_add (add_le_add h₁ h₂) h₃

/-- Single-pair late local-CLT error in summable-weight form. -/
theorem abs_fourierProductMass_sub_radialGaussianMass_late_weights
    {n d e ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hn : 64 * ρ ≤ n) :
    |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| ≤
      (16 * (ρ : ℝ) * (radiusSq d e : ℝ) +
          (radiusSq d e : ℝ)) *
        cubeGaussianWeight (radiusSq d e) (n - 1) +
      (2 / 3 : ℝ) * squareGaussianWeight (radiusSq d e) (n - 1) := by
  have hn0 : 0 < n := by omega
  have hraw := abs_fourierProductMass_sub_radialGaussianMass_late_le
    hρ hdρ heρ hradius hn
  have hpi : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hden : (n : ℝ) ≤ Real.pi * n := by nlinarith
  have hprefactor :
      Real.exp (-(radiusSq d e : ℝ) / (2 * n)) / (Real.pi * n) ≤
        Real.exp (-(radiusSq d e : ℝ) / (2 * n)) / n :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hnR hden
  have henvelope : 0 ≤
      16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
        (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ)) := by
    positivity
  calc
    |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| ≤
      Real.exp (-(radiusSq d e : ℝ) / (2 * n)) / (Real.pi * n) *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ))) := hraw
    _ ≤ Real.exp (-(radiusSq d e : ℝ) / (2 * n)) / n *
        (16 * (ρ : ℝ) * (radiusSq d e : ℝ) / (n : ℝ) ^ 2 +
          (radiusSq d e : ℝ) / (n : ℝ) ^ 2 + 2 / (3 * (n : ℝ))) := by
      gcongr
    _ = (16 * (ρ : ℝ) * (radiusSq d e : ℝ) +
          (radiusSq d e : ℝ)) *
        cubeGaussianWeight (radiusSq d e) (n - 1) +
      (2 / 3 : ℝ) * squareGaussianWeight (radiusSq d e) (n - 1) := by
      rw [squareGaussianWeight_pred hn0, cubeGaussianWeight_pred hn0]
      ring

/-- The radial-main-term gap is a single square Gaussian weight. -/
theorem abs_radialGaussianMass_sub_le_squareWeight
    {Q Q' n : ℕ} (hn : 0 < n) :
    |radialGaussianMass Q n - radialGaussianMass Q' n| ≤
      |(Q : ℝ) - (Q' : ℝ)| *
        squareGaussianWeight (min Q Q') (n - 1) := by
  have hraw := abs_radialGaussianMass_sub_le (Q := Q) (Q' := Q') hn
  have hgap : 0 ≤ |(Q : ℝ) - (Q' : ℝ)| := abs_nonneg _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hden : (n : ℝ) ≤ Real.pi * n := by nlinarith
  have hexp : Real.exp (-(min Q Q' : ℝ) / n) ≤
      Real.exp (-(min Q Q' : ℝ) / (2 * n)) := by
    apply Real.exp_le_exp.mpr
    have hq : (0 : ℝ) ≤ min (Q : ℝ) (Q' : ℝ) := by positivity
    have : (min Q Q' : ℝ) / (2 * n) ≤ (min Q Q' : ℝ) / n := by
      exact div_le_div_of_nonneg_left hq hnR (by nlinarith)
    rw [show -(min Q Q' : ℝ) / n = -((min Q Q' : ℝ) / n) by ring,
      show -(min Q Q' : ℝ) / (2 * n) =
        -((min Q Q' : ℝ) / (2 * n)) by ring]
    exact neg_le_neg this
  have hgauss : Real.exp (-(min Q Q' : ℝ) / n) / (Real.pi * n) ≤
      Real.exp (-(min Q Q' : ℝ) / (2 * n)) / n := by
    calc
      Real.exp (-(min Q Q' : ℝ) / n) / (Real.pi * n) ≤
          Real.exp (-(min Q Q' : ℝ) / n) / n :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hnR hden
      _ ≤ Real.exp (-(min Q Q' : ℝ) / (2 * n)) / n := by gcongr
  have hgauss' : Real.exp (-((min Q Q' : ℕ) : ℝ) / n) / (Real.pi * n) ≤
      Real.exp (-((min Q Q' : ℕ) : ℝ) / (2 * n)) / n := by
    simpa using hgauss
  calc
    |radialGaussianMass Q n - radialGaussianMass Q' n| ≤
      (|(Q : ℝ) - (Q' : ℝ)| / n) *
        (Real.exp (-(min Q Q' : ℕ) / n) / (Real.pi * n)) := hraw
    _ ≤ (|(Q : ℝ) - (Q' : ℝ)| / n) *
        (Real.exp (-(min Q Q' : ℕ) / (2 * n)) / n) :=
      mul_le_mul_of_nonneg_left hgauss' (div_nonneg hgap hnR.le)
    _ = |(Q : ℝ) - (Q' : ℝ)| *
        squareGaussianWeight (min Q Q') (n - 1) := by
      rw [squareGaussianWeight_pred hn]
      ring

/-- Nearby-radius product masses expressed as five summable weights. -/
theorem abs_fourierProductMass_sub_le_late_weights
    {n d e d' e' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hdρ' : d' ≤ 2 * ρ) (heρ' : e' ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hn : 64 * ρ ≤ n) :
    |fourierProductMass n d e - fourierProductMass n d' e'| ≤
      (16 * (ρ : ℝ) * (radiusSq d e : ℝ) + (radiusSq d e : ℝ)) *
          cubeGaussianWeight (radiusSq d e) (n - 1) +
        (2 / 3 : ℝ) * squareGaussianWeight (radiusSq d e) (n - 1) +
      |(radiusSq d e : ℝ) - (radiusSq d' e' : ℝ)| *
          squareGaussianWeight (min (radiusSq d e) (radiusSq d' e')) (n - 1) +
      (16 * (ρ : ℝ) * (radiusSq d' e' : ℝ) + (radiusSq d' e' : ℝ)) *
          cubeGaussianWeight (radiusSq d' e') (n - 1) +
        (2 / 3 : ℝ) * squareGaussianWeight (radiusSq d' e') (n - 1) := by
  have hn0 : 0 < n := by omega
  have h₁ := abs_fourierProductMass_sub_radialGaussianMass_late_weights
    hρ hdρ heρ hradius hn
  have h₂ := abs_radialGaussianMass_sub_le_squareWeight
    (Q := radiusSq d e) (Q' := radiusSq d' e') hn0
  have h₃ := abs_fourierProductMass_sub_radialGaussianMass_late_weights
    hρ hdρ' heρ' hradius' hn
  calc
    |fourierProductMass n d e - fourierProductMass n d' e'| =
        |(fourierProductMass n d e - radialGaussianMass (radiusSq d e) n) +
          (radialGaussianMass (radiusSq d e) n -
            radialGaussianMass (radiusSq d' e') n) +
          (radialGaussianMass (radiusSq d' e') n -
            fourierProductMass n d' e')| := by ring_nf
    _ ≤ |fourierProductMass n d e - radialGaussianMass (radiusSq d e) n| +
        |radialGaussianMass (radiusSq d e) n -
          radialGaussianMass (radiusSq d' e') n| +
        |radialGaussianMass (radiusSq d' e') n -
          fourierProductMass n d' e'| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [abs_sub_comm (radialGaussianMass (radiusSq d' e') n)]
      linarith

lemma tsum_squareGaussianWeight_shift_le (Q K : ℕ) :
    ∑' n : ℕ, squareGaussianWeight Q (n + K) ≤
      ∑' n : ℕ, squareGaussianWeight Q n := by
  have hs := summable_squareGaussianWeight Q
  rw [← hs.sum_add_tsum_nat_add K]
  have : 0 ≤ ∑ n ∈ Finset.range K, squareGaussianWeight Q n := by
    apply Finset.sum_nonneg
    intro n _
    unfold squareGaussianWeight
    positivity
  linarith

lemma tsum_cubeGaussianWeight_shift_le (Q K : ℕ) :
    ∑' n : ℕ, cubeGaussianWeight Q (n + K) ≤
      ∑' n : ℕ, cubeGaussianWeight Q n := by
  have hs := summable_cubeGaussianWeight Q
  rw [← hs.sum_add_tsum_nat_add K]
  have : 0 ≤ ∑ n ∈ Finset.range K, cubeGaussianWeight Q n := by
    apply Finset.sum_nonneg
    intro n _
    unfold cubeGaussianWeight
    positivity
  linarith

/-- Summed bound for one of the two local-CLT error packets. -/
lemma tsum_localErrorWeight_shift_le {Q ρ K : ℕ}
    (hρ : 1 ≤ ρ) (hQlo : ρ ^ 2 ≤ Q) :
    (∑' n : ℕ, (
        (16 * (ρ : ℝ) * (Q : ℝ) + (Q : ℝ)) *
            cubeGaussianWeight Q (n + K) +
          (2 / 3 : ℝ) * squareGaussianWeight Q (n + K))) ≤
      7500 / (ρ : ℝ) := by
  have hρR : (0 : ℝ) < ρ := by positivity
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity : 0 < ρ ^ 2) hQlo
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hQloR : (ρ : ℝ) ^ 2 ≤ Q := by exact_mod_cast hQlo
  let C : ℝ := 16 * (ρ : ℝ) * Q + Q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcSum : Summable (fun n : ℕ ↦ C * cubeGaussianWeight Q (n + K)) :=
    ((summable_nat_add_iff K).mpr (summable_cubeGaussianWeight Q)).mul_left C
  have hcSum' : Summable (fun n : ℕ ↦
      (16 * (ρ : ℝ) * (Q : ℝ) + (Q : ℝ)) *
        cubeGaussianWeight Q (n + K)) := by
    simpa [C] using hcSum
  have hsSum : Summable (fun n : ℕ ↦
      (2 / 3 : ℝ) * squareGaussianWeight Q (n + K)) :=
    ((summable_nat_add_iff K).mpr (summable_squareGaussianWeight Q)).mul_left _
  have hcTail := (tsum_cubeGaussianWeight_shift_le Q K).trans
    (tsum_cubeGaussianWeight_le hQpos)
  have hsTail := (tsum_squareGaussianWeight_shift_le Q K).trans
    (tsum_squareGaussianWeight_le hQpos)
  have hInv : (1 : ℝ) / Q ≤ 1 / (ρ : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hρR) hQloR
  calc
    _ =
      (∑' n : ℕ, (16 * (ρ : ℝ) * (Q : ℝ) + (Q : ℝ)) *
          cubeGaussianWeight Q (n + K)) +
        ∑' n : ℕ, (2 / 3 : ℝ) * squareGaussianWeight Q (n + K) :=
      Summable.tsum_add hcSum' hsSum
    _ = C * (∑' n : ℕ, cubeGaussianWeight Q (n + K)) +
        (2 / 3 : ℝ) * (∑' n : ℕ, squareGaussianWeight Q (n + K)) := by
      rw [tsum_mul_left, tsum_mul_left]
    _ ≤ C * (400 / (Q : ℝ) ^ 2) +
        (2 / 3 : ℝ) * (400 / (Q : ℝ)) := by gcongr
    _ = (6400 * (ρ : ℝ) + 400 + 800 / 3) * (1 / (Q : ℝ)) := by
      dsimp [C]
      field_simp
      ring
    _ ≤ (6400 * (ρ : ℝ) + 400 + 800 / 3) *
        (1 / (ρ : ℝ) ^ 2) := by gcongr
    _ ≤ 7500 / (ρ : ℝ) := by
      field_simp
      nlinarith [show (1 : ℝ) ≤ ρ by exact_mod_cast hρ]

/-- Summed Gaussian main-term error when the squared radii differ by at most
`L rho`. -/
lemma tsum_radialGapWeight_shift_le {Qmin ρ L K : ℕ} {Δ : ℝ}
    (hρ : 1 ≤ ρ) (hQlo : ρ ^ 2 ≤ Qmin)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ (L : ℝ) * ρ) :
    ∑' n : ℕ, Δ * squareGaussianWeight Qmin (n + K) ≤
      400 * (L : ℝ) / (ρ : ℝ) := by
  have hρR : (0 : ℝ) < ρ := by positivity
  have hQpos : 0 < Qmin := lt_of_lt_of_le (by positivity : 0 < ρ ^ 2) hQlo
  have hQloR : (ρ : ℝ) ^ 2 ≤ Qmin := by exact_mod_cast hQlo
  have hsSum : Summable (fun n : ℕ ↦
      Δ * squareGaussianWeight Qmin (n + K)) :=
    ((summable_nat_add_iff K).mpr
      (summable_squareGaussianWeight Qmin)).mul_left Δ
  have hsTail := (tsum_squareGaussianWeight_shift_le Qmin K).trans
    (tsum_squareGaussianWeight_le hQpos)
  have hInv : (1 : ℝ) / Qmin ≤ 1 / (ρ : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hρR) hQloR
  calc
    ∑' n : ℕ, Δ * squareGaussianWeight Qmin (n + K) =
        Δ * (∑' n : ℕ, squareGaussianWeight Qmin (n + K)) := by
      rw [tsum_mul_left]
    _ ≤ Δ * (400 / (Qmin : ℝ)) := by gcongr
    _ ≤ ((L : ℝ) * ρ) * (400 * (1 / (ρ : ℝ) ^ 2)) := by
      have htail' : 400 / (Qmin : ℝ) ≤ 400 * (1 / (ρ : ℝ) ^ 2) := by
        calc
          400 / (Qmin : ℝ) = 400 * (1 / (Qmin : ℝ)) := by ring
          _ ≤ 400 * (1 / (ρ : ℝ) ^ 2) := by gcongr
      exact mul_le_mul hΔ htail' (by positivity) (by positivity)
    _ = 400 * (L : ℝ) / (ρ : ℝ) := by field_simp

/-- **Radial Fourier-potential comparison.**  In a diagonal box of radius
`2 rho`, two points on the same Euclidean circle have potentials differing
by `O(rho⁻¹)`.  The numerical constant is deliberately generous; the key
content is the inverse-radius decay and the absence of angular dependence. -/
theorem abs_fourierPotential_sub_le_of_radiusSq_eq
    {d e d' e' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hdρ' : d' ≤ 2 * ρ) (heρ' : e' ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hQ : radiusSq d e = radiusSq d' e') :
    |fourierPotential d e - fourierPotential d' e'| ≤
      1611000000 / (ρ : ℝ) := by
  let M : ℕ := 64 * ρ
  let K : ℕ := M - 1
  let Q : ℕ := radiusSq d e
  let f : ℕ → ℝ := fun n ↦
    fourierProductLoss d e n - fourierProductLoss d' e' n
  have hρpos : 0 < ρ := by omega
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρpos
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hQloNat : ρ ^ 2 ≤ Q := by
    dsimp [Q, radiusSq]
    rcases max_cases d e with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_right _ _)
    · rw [hm] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_left _ _)
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity : 0 < ρ ^ 2) hQloNat
  have hQlo : (ρ : ℝ) ^ 2 ≤ Q := by exact_mod_cast hQloNat
  have hQupperNat : Q ≤ 8 * ρ ^ 2 := by
    dsimp [Q, radiusSq]
    have hd2 := Nat.pow_le_pow_left hdρ 2
    have he2 := Nat.pow_le_pow_left heρ 2
    nlinarith
  have hQupper : (Q : ℝ) ≤ 8 * (ρ : ℝ) ^ 2 := by exact_mod_cast hQupperNat
  have hfSummable : Summable f := by
    dsimp [f]
    exact (summable_fourierProductLoss d e).sub
      (summable_fourierProductLoss d' e')
  have hfAbsSummable : Summable (fun n ↦ |f n|) := by
    simpa only [Real.norm_eq_abs] using hfSummable.norm
  have hearlyPoint (n : ℕ) (hn : n ∈ Finset.range M) :
      |f n| ≤ 25165824 / (ρ : ℝ) ^ 3 := by
    have hmass := abs_fourierProductMass_sub_le_of_radiusSq_eq_early
      hρ hradius hradius' (by simpa [M] using Finset.mem_range.mp hn)
    dsimp [f, fourierProductLoss]
    rw [show
      (fourierProductMass n 0 0 - fourierProductMass n d e) -
          (fourierProductMass n 0 0 - fourierProductMass n d' e') =
        fourierProductMass n d' e' - fourierProductMass n d e by ring,
      abs_sub_comm]
    exact hmass
  have hearly :
      |∑ n ∈ Finset.range M, f n| ≤ 1610612736 / (ρ : ℝ) ^ 2 := by
    calc
      |∑ n ∈ Finset.range M, f n| ≤
          ∑ n ∈ Finset.range M, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.range M, 25165824 / (ρ : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hearlyPoint n hn
      _ = 1610612736 / (ρ : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp [M]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        field_simp
        ring
  let C : ℝ := 32 * (ρ : ℝ) * Q + 2 * Q
  let G : ℕ → ℝ := fun n ↦
    C * cubeGaussianWeight Q (n + K) +
      (4 / 3 : ℝ) * squareGaussianWeight Q (n + K)
  have hCSummable : Summable (fun n : ℕ ↦
      C * cubeGaussianWeight Q (n + K)) :=
    ((summable_nat_add_iff K).mpr (summable_cubeGaussianWeight Q)).mul_left C
  have hSSummable : Summable (fun n : ℕ ↦
      (4 / 3 : ℝ) * squareGaussianWeight Q (n + K)) :=
    ((summable_nat_add_iff K).mpr (summable_squareGaussianWeight Q)).mul_left _
  have hGSummable : Summable G := hCSummable.add hSSummable
  have hlatePoint (n : ℕ) : |f (n + M)| ≤ G n := by
    have hmass := abs_fourierProductMass_sub_le_of_radiusSq_eq_late_weights
      hρ hdρ heρ hdρ' heρ' hradius hradius' hQ
      (show M ≤ n + M by omega)
    have hindex : n + M - 1 = n + K := by dsimp [K]; omega
    dsimp [f, fourierProductLoss]
    rw [show
      (fourierProductMass (n + M) 0 0 - fourierProductMass (n + M) d e) -
          (fourierProductMass (n + M) 0 0 -
            fourierProductMass (n + M) d' e') =
        fourierProductMass (n + M) d' e' -
          fourierProductMass (n + M) d e by ring,
      abs_sub_comm]
    dsimp [G, C, Q]
    rw [hindex] at hmass
    convert hmass using 1 <;> ring
  have hlateAbsSummable : Summable (fun n : ℕ ↦ |f (n + M)|) := by
    exact (summable_nat_add_iff M).mpr hfAbsSummable
  have hlateRaw : ∑' n : ℕ, |f (n + M)| ≤ ∑' n : ℕ, G n := by
    exact Summable.tsum_le_tsum hlatePoint hlateAbsSummable hGSummable
  have hcubeTail := tsum_cubeGaussianWeight_shift_le Q K
  have hsquareTail := tsum_squareGaussianWeight_shift_le Q K
  have hcubeTotal := tsum_cubeGaussianWeight_le hQpos
  have hsquareTotal := tsum_squareGaussianWeight_le hQpos
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hlateMajorant : ∑' n : ℕ, G n ≤ 15000 / (ρ : ℝ) := by
    have hcubeTail' : ∑' n : ℕ, cubeGaussianWeight Q (n + K) ≤
        400 / (Q : ℝ) ^ 2 := hcubeTail.trans hcubeTotal
    have hsquareTail' : ∑' n : ℕ, squareGaussianWeight Q (n + K) ≤
        400 / (Q : ℝ) := hsquareTail.trans hsquareTotal
    have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQpos
    have hInv : (1 : ℝ) / Q ≤ 1 / (ρ : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hρR) hQlo
    calc
      ∑' n : ℕ, G n =
          C * (∑' n : ℕ, cubeGaussianWeight Q (n + K)) +
            (4 / 3 : ℝ) *
              (∑' n : ℕ, squareGaussianWeight Q (n + K)) := by
        dsimp [G]
        rw [Summable.tsum_add hCSummable hSSummable,
          tsum_mul_left, tsum_mul_left]
      _ ≤ C * (400 / (Q : ℝ) ^ 2) +
          (4 / 3 : ℝ) * (400 / (Q : ℝ)) := by gcongr
      _ = (12800 * (ρ : ℝ) + 800) * (1 / (Q : ℝ)) +
          (1600 / 3 : ℝ) * (1 / (Q : ℝ)) := by
        dsimp [C]
        field_simp
        ring
      _ ≤ (12800 * (ρ : ℝ) + 800) * (1 / (ρ : ℝ) ^ 2) +
          (1600 / 3 : ℝ) * (1 / (ρ : ℝ) ^ 2) := by
        gcongr
      _ ≤ 15000 / (ρ : ℝ) := by
        field_simp
        nlinarith [show (1 : ℝ) ≤ ρ by exact_mod_cast (show 1 ≤ ρ by omega)]
  have hlate : |∑' n : ℕ, f (n + M)| ≤ 15000 / (ρ : ℝ) := by
    calc
      |∑' n : ℕ, f (n + M)| = ‖∑' n : ℕ, f (n + M)‖ := rfl
      _ ≤ ∑' n : ℕ, ‖f (n + M)‖ :=
        norm_tsum_le_tsum_norm (by
          simpa only [Real.norm_eq_abs] using hlateAbsSummable)
      _ = ∑' n : ℕ, |f (n + M)| := by
        apply tsum_congr
        intro n
        rfl
      _ ≤ 15000 / (ρ : ℝ) := hlateRaw.trans hlateMajorant
  have hsplit := hfSummable.sum_add_tsum_nat_add M
  unfold fourierPotential
  rw [← Summable.tsum_sub (summable_fourierProductLoss d e)
    (summable_fourierProductLoss d' e'), ← hsplit]
  calc
    |(∑ n ∈ Finset.range M, f n) + ∑' n : ℕ, f (n + M)| ≤
        |∑ n ∈ Finset.range M, f n| + |∑' n : ℕ, f (n + M)| := abs_add_le _ _
    _ ≤ 1610612736 / (ρ : ℝ) ^ 2 + 15000 / (ρ : ℝ) :=
      add_le_add hearly hlate
    _ ≤ 1611000000 / (ρ : ℝ) := by
      field_simp
      nlinarith [show (1 : ℝ) ≤ ρ by exact_mod_cast (show 1 ≤ ρ by omega)]

/-- Nearby-radius version of the radial potential comparison.  If the two
squared radii differ by at most `L rho`, the error is still `O(rho⁻¹)`, with
linear dependence on `L`. -/
theorem abs_fourierPotential_sub_le_of_radiusSq_gap
    {d e d' e' ρ L : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hdρ' : d' ≤ 2 * ρ) (heρ' : e' ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hgap : |(radiusSq d e : ℝ) - (radiusSq d' e' : ℝ)| ≤
      (L : ℝ) * ρ) :
    |fourierPotential d e - fourierPotential d' e'| ≤
      (1611000000 + 1000 * (L : ℝ)) / (ρ : ℝ) := by
  let M : ℕ := 64 * ρ
  let K : ℕ := M - 1
  let Q : ℕ := radiusSq d e
  let Q' : ℕ := radiusSq d' e'
  let Qmin : ℕ := min Q Q'
  let Δ : ℝ := |(Q : ℝ) - (Q' : ℝ)|
  let f : ℕ → ℝ := fun n ↦
    fourierProductLoss d e n - fourierProductLoss d' e' n
  have hρone : 1 ≤ ρ := by omega
  have hρpos : 0 < ρ := by omega
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρpos
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hQlo : ρ ^ 2 ≤ Q := by
    dsimp [Q, radiusSq]
    rcases max_cases d e with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_right _ _)
    · rw [hm] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_left _ _)
  have hQlo' : ρ ^ 2 ≤ Q' := by
    dsimp [Q', radiusSq]
    rcases max_cases d' e' with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm] at hradius'
      exact (Nat.pow_le_pow_left hradius' 2).trans (Nat.le_add_right _ _)
    · rw [hm] at hradius'
      exact (Nat.pow_le_pow_left hradius' 2).trans (Nat.le_add_left _ _)
  have hQminlo : ρ ^ 2 ≤ Qmin := by
    dsimp [Qmin]
    exact le_min hQlo hQlo'
  have hΔ0 : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hΔ : Δ ≤ (L : ℝ) * ρ := by
    simpa [Δ, Q, Q'] using hgap
  have hfSummable : Summable f := by
    dsimp [f]
    exact (summable_fourierProductLoss d e).sub
      (summable_fourierProductLoss d' e')
  have hfAbsSummable : Summable (fun n ↦ |f n|) := by
    simpa only [Real.norm_eq_abs] using hfSummable.norm
  have hearlyPoint (n : ℕ) (hn : n ∈ Finset.range M) :
      |f n| ≤ 25165824 / (ρ : ℝ) ^ 3 := by
    have hmass := abs_fourierProductMass_sub_le_of_radiusSq_eq_early
      hρ hradius hradius' (by simpa [M] using Finset.mem_range.mp hn)
    dsimp [f, fourierProductLoss]
    rw [show
      (fourierProductMass n 0 0 - fourierProductMass n d e) -
          (fourierProductMass n 0 0 - fourierProductMass n d' e') =
        fourierProductMass n d' e' - fourierProductMass n d e by ring,
      abs_sub_comm]
    exact hmass
  have hearly :
      |∑ n ∈ Finset.range M, f n| ≤ 1610612736 / (ρ : ℝ) ^ 2 := by
    calc
      |∑ n ∈ Finset.range M, f n| ≤
          ∑ n ∈ Finset.range M, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.range M, 25165824 / (ρ : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hearlyPoint n hn
      _ = 1610612736 / (ρ : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp [M]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        field_simp
        ring
  let G₁ : ℕ → ℝ := fun n ↦
    (16 * (ρ : ℝ) * (Q : ℝ) + (Q : ℝ)) *
        cubeGaussianWeight Q (n + K) +
      (2 / 3 : ℝ) * squareGaussianWeight Q (n + K)
  let G₂ : ℕ → ℝ := fun n ↦
    Δ * squareGaussianWeight Qmin (n + K)
  let G₃ : ℕ → ℝ := fun n ↦
    (16 * (ρ : ℝ) * (Q' : ℝ) + (Q' : ℝ)) *
        cubeGaussianWeight Q' (n + K) +
      (2 / 3 : ℝ) * squareGaussianWeight Q' (n + K)
  let G : ℕ → ℝ := fun n ↦ G₁ n + G₂ n + G₃ n
  have hG₁Summable : Summable G₁ := by
    dsimp [G₁]
    exact (((summable_nat_add_iff K).mpr (summable_cubeGaussianWeight Q)).mul_left _).add
      (((summable_nat_add_iff K).mpr (summable_squareGaussianWeight Q)).mul_left _)
  have hG₂Summable : Summable G₂ := by
    dsimp [G₂]
    exact ((summable_nat_add_iff K).mpr
      (summable_squareGaussianWeight Qmin)).mul_left Δ
  have hG₃Summable : Summable G₃ := by
    dsimp [G₃]
    exact (((summable_nat_add_iff K).mpr (summable_cubeGaussianWeight Q')).mul_left _).add
      (((summable_nat_add_iff K).mpr (summable_squareGaussianWeight Q')).mul_left _)
  have hGSummable : Summable G := by
    dsimp [G]
    exact (hG₁Summable.add hG₂Summable).add hG₃Summable
  have hlatePoint (n : ℕ) : |f (n + M)| ≤ G n := by
    have hmass := abs_fourierProductMass_sub_le_late_weights
      hρ hdρ heρ hdρ' heρ' hradius hradius'
      (show M ≤ n + M by omega)
    have hindex : n + M - 1 = n + K := by dsimp [K]; omega
    dsimp [f, fourierProductLoss]
    rw [show
      (fourierProductMass (n + M) 0 0 - fourierProductMass (n + M) d e) -
          (fourierProductMass (n + M) 0 0 -
            fourierProductMass (n + M) d' e') =
        fourierProductMass (n + M) d' e' -
          fourierProductMass (n + M) d e by ring,
      abs_sub_comm]
    dsimp [G, G₁, G₂, G₃, Δ, Qmin, Q, Q']
    rw [hindex] at hmass
    convert hmass using 1 <;> ring
  have hlateAbsSummable : Summable (fun n : ℕ ↦ |f (n + M)|) :=
    (summable_nat_add_iff M).mpr hfAbsSummable
  have hlateRaw : ∑' n : ℕ, |f (n + M)| ≤ ∑' n : ℕ, G n :=
    Summable.tsum_le_tsum hlatePoint hlateAbsSummable hGSummable
  have hG₁Bound : ∑' n : ℕ, G₁ n ≤ 7500 / (ρ : ℝ) := by
    simpa [G₁] using
      (tsum_localErrorWeight_shift_le (Q := Q) (ρ := ρ) (K := K) hρone hQlo)
  have hG₂Bound : ∑' n : ℕ, G₂ n ≤ 400 * (L : ℝ) / (ρ : ℝ) := by
    simpa [G₂] using
      (tsum_radialGapWeight_shift_le (Qmin := Qmin) (ρ := ρ) (L := L)
        (K := K) hρone hQminlo hΔ0 hΔ)
  have hG₃Bound : ∑' n : ℕ, G₃ n ≤ 7500 / (ρ : ℝ) := by
    simpa [G₃] using
      (tsum_localErrorWeight_shift_le (Q := Q') (ρ := ρ) (K := K) hρone hQlo')
  have hlateMajorant : ∑' n : ℕ, G n ≤
      (15000 + 400 * (L : ℝ)) / (ρ : ℝ) := by
    calc
      ∑' n : ℕ, G n =
          (∑' n : ℕ, G₁ n) + (∑' n : ℕ, G₂ n) + ∑' n : ℕ, G₃ n := by
        dsimp [G]
        rw [Summable.tsum_add (hG₁Summable.add hG₂Summable) hG₃Summable,
          Summable.tsum_add hG₁Summable hG₂Summable]
      _ ≤ 7500 / (ρ : ℝ) + 400 * (L : ℝ) / (ρ : ℝ) +
          7500 / (ρ : ℝ) := add_le_add (add_le_add hG₁Bound hG₂Bound) hG₃Bound
      _ = (15000 + 400 * (L : ℝ)) / (ρ : ℝ) := by ring
  have hlate : |∑' n : ℕ, f (n + M)| ≤
      (15000 + 400 * (L : ℝ)) / (ρ : ℝ) := by
    calc
      |∑' n : ℕ, f (n + M)| = ‖∑' n : ℕ, f (n + M)‖ := rfl
      _ ≤ ∑' n : ℕ, ‖f (n + M)‖ :=
        norm_tsum_le_tsum_norm (by
          simpa only [Real.norm_eq_abs] using hlateAbsSummable)
      _ = ∑' n : ℕ, |f (n + M)| := by
        apply tsum_congr
        intro n
        rfl
      _ ≤ (15000 + 400 * (L : ℝ)) / (ρ : ℝ) :=
        hlateRaw.trans hlateMajorant
  have hsplit := hfSummable.sum_add_tsum_nat_add M
  unfold fourierPotential
  rw [← Summable.tsum_sub (summable_fourierProductLoss d e)
    (summable_fourierProductLoss d' e'), ← hsplit]
  calc
    |(∑ n ∈ Finset.range M, f n) + ∑' n : ℕ, f (n + M)| ≤
        |∑ n ∈ Finset.range M, f n| + |∑' n : ℕ, f (n + M)| := abs_add_le _ _
    _ ≤ 1610612736 / (ρ : ℝ) ^ 2 +
        (15000 + 400 * (L : ℝ)) / (ρ : ℝ) := add_le_add hearly hlate
    _ ≤ (1611000000 + 1000 * (L : ℝ)) / (ρ : ℝ) := by
      field_simp
      have hL0 : (0 : ℝ) ≤ L := by positivity
      nlinarith [show (1 : ℝ) ≤ ρ by exact_mod_cast hρone]

end PotentialRadialMass
end Erdos1165
