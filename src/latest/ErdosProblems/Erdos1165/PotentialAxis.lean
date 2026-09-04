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

import ErdosProblems.Erdos1165.PotentialGradient
import ErdosProblems.Erdos1165.OffDiagonal
import ErdosProblems.Erdos1165.PotentialHarmonicRate

/-!
# Exact potential-kernel increments on an axis

The positive series for an adjacent Fourier-coordinate potential increment
is hypergeometric on a coordinate axis.  Its finite sums telescope by an
exact Gosper identity.  The endpoint is evaluated from the sharp Wallis
limit for the planar return probability, giving the exact increment
`4 / (π * (2d + 1))`.
-/

open Filter Real
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialAxis

open BinomialGaussian PotentialFourierIntegral PotentialGradient
  PotentialHarmonicRate

/-- The product of a displaced and a centered one-dimensional mass. -/
noncomputable def axisMass (d n : ℕ) : ℝ :=
  evenSymmetricMass n d * evenSymmetricMass n 0

/-- The Gosper antiderivative of the positive axis-gradient summand. -/
noncomputable def axisAntiderivative (d n : ℕ) : ℝ :=
  4 * (n - d : ℕ) / (2 * d + 1 : ℕ) * axisMass d n

/-- Exact time recurrence for a fixed displaced centered-binomial mass. -/
lemma evenSymmetricMass_time_succ_mul {d n : ℕ} (hd : d ≤ n) :
    2 * (n + d + 1 : ℝ) * (n - d + 1 : ℝ) *
        evenSymmetricMass (n + 1) d =
      (n + 1 : ℝ) * (2 * n + 1 : ℝ) * evenSymmetricMass n d := by
  have hright := Nat.choose_succ_right_eq (2 * n + 2) (n + d)
  have hrow₁ := Nat.choose_mul_succ_eq (2 * n + 1) (n + d)
  have hrow₀ := Nat.choose_mul_succ_eq (2 * n) (n + d)
  have hA : (2 * n + 2).choose (n + d + 1) * (n + d + 1) =
      (2 * n + 1).choose (n + d) * (2 * n + 2) := by
    rw [hright]
    rw [hrow₁]
  have hB : (2 * n + 1).choose (n + d) * (n - d + 1) =
      (2 * n).choose (n + d) * (2 * n + 1) := by
    rw [hrow₀]
    congr
    omega
  have hchoose :
      (2 * n + 2).choose (n + d + 1) * (n + d + 1) * (n - d + 1) =
        (2 * n).choose (n + d) * (2 * n + 1) * (2 * n + 2) := by
    calc
      (2 * n + 2).choose (n + d + 1) * (n + d + 1) * (n - d + 1) =
          ((2 * n + 1).choose (n + d) * (2 * n + 2)) * (n - d + 1) := by
            rw [hA]
      _ = ((2 * n + 1).choose (n + d) * (n - d + 1)) * (2 * n + 2) := by ring
      _ = ((2 * n).choose (n + d) * (2 * n + 1)) * (2 * n + 2) := by rw [hB]
      _ = (2 * n).choose (n + d) * (2 * n + 1) * (2 * n + 2) := by ring
  have hchooseR :
      ((2 * n + 2).choose (n + d + 1) : ℝ) * (n + d + 1) * (n - d + 1) =
        ((2 * n).choose (n + d) : ℝ) * (2 * n + 1) * (2 * n + 2) := by
    exact_mod_cast hchoose
  unfold evenSymmetricMass symBinomialMass
  rw [show 2 * (n + 1) = 2 * n + 2 by omega,
    show n + 1 + d = n + d + 1 by omega, pow_succ]
  field_simp
  rw [show (2 : ℝ) ^ (2 * n + 1) = 2 * 2 ^ (2 * n) by rw [pow_succ]; ring]
  linear_combination (2 : ℝ) ^ (2 * n) * hchooseR

/-- Exact one-step recurrence for the axis product mass. -/
lemma axisMass_time_succ_mul {d n : ℕ} (hd : d ≤ n) :
    4 * (n - d + 1 : ℝ) * (n + d + 1 : ℝ) * axisMass d (n + 1) =
      (2 * n + 1 : ℝ) ^ 2 * axisMass d n := by
  have hD := evenSymmetricMass_time_succ_mul (d := d) (n := n) hd
  have h0 := evenSymmetricMass_time_succ_mul (d := 0) (n := n) (by omega)
  have hprod := congrArg₂ (fun x y : ℝ ↦ x * y) hD h0
  unfold axisMass
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero,
    Nat.sub_zero, zero_add] at hprod ⊢
  have hn : (0 : ℝ) < n + 1 := by positivity
  nlinarith [hprod]

/-- Gosper's finite-difference identity, including the zero part before the
support of the displaced binomial mass begins. -/
theorem axisAntiderivative_succ_sub (d n : ℕ) :
    axisAntiderivative d (n + 1) - axisAntiderivative d n =
      firstGradientTerm d 0 n := by
  by_cases hd : d ≤ n
  · have hrec := axisMass_time_succ_mul (d := d) (n := n) hd
    have hgrad := firstGradientTerm_eq (d := d) (e := 0) hd
    rw [hgrad]
    unfold fourierProductMass
    change axisAntiderivative d (n + 1) - axisAntiderivative d n =
      axisMass d n * (((2 * d + 1 : ℕ) : ℝ) / (n + d + 1 : ℝ))
    unfold axisAntiderivative
    have hsub : n + 1 - d = n - d + 1 := by omega
    rw [hsub]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    rw [Nat.cast_sub hd]
    have hden₁ : (2 * (d : ℝ) + 1) ≠ 0 := by positivity
    have hden₂ : (n : ℝ) + d + 1 ≠ 0 := by positivity
    field_simp
    linear_combination hrec
  · have hnd : n < d := Nat.lt_of_not_ge hd
    have hsucc : n + 1 ≤ d := by omega
    rw [firstGradientTerm_eq_zero_of_lt hnd]
    simp [axisAntiderivative, Nat.sub_eq_zero_of_le hnd.le,
      Nat.sub_eq_zero_of_le hsucc]

/-- Exact finite partial sum of the positive axis gradient. -/
theorem sum_firstGradientTerm_axis (d N : ℕ) :
    ∑ n ∈ Finset.range N, firstGradientTerm d 0 n = axisAntiderivative d N := by
  induction N with
  | zero => simp [axisAntiderivative]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      linarith [axisAntiderivative_succ_sub d N]

private theorem tendsto_nat_mul_axisLoss_zero (d : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * fourierProductLoss d 0 n) atTop (nhds 0) := by
  let C : ℝ := 10 * ((d + 1 : ℝ) ^ 2 + 1)
  have hupper : Tendsto (fun n : ℕ ↦ C * (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C :
        Tendsto (fun n : ℕ ↦ C * (1 / (n + 1 : ℝ))) atTop (nhds (C * 0)))
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ mul_nonneg (by positivity)
      (fourierProductLoss_nonneg d 0 n))
    ?_ hupper
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := by omega
  have hloss := fourierProductLoss_quadratic_le (d := d) (e := 0) hn0
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, one_pow] at hloss
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  dsimp [C]
  calc
    (n : ℝ) * fourierProductLoss d 0 n ≤
        (n : ℝ) *
          (10 * ((d + 1 : ℝ) ^ 2 + 1) /
            ((n : ℝ) * (n + 1))) :=
      mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = 10 * ((d + 1 : ℝ) ^ 2 + 1) * (1 / (n + 1 : ℝ)) := by
      field_simp

private theorem tendsto_nat_mul_axisMass (d : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * axisMass d n) atTop (nhds (1 / Real.pi)) := by
  have h := tendsto_mul_planarReturnProbability.sub (tendsto_nat_mul_axisLoss_zero d)
  convert h using 1
  · funext n
    unfold axisMass fourierProductLoss
    rw [fourierProductMass_center]
    unfold fourierProductMass
    ring
  · ring_nf

private theorem tendsto_natSub_div_nat_one (d : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n - d : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
  have hmain : Tendsto (fun n : ℕ ↦ 1 - (d : ℝ) / n) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hzero using 1
    all_goals ring_nf
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop d, eventually_ge_atTop 1] with n hn hn1
  rw [Nat.cast_sub hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- The Gosper endpoint converges to the exact Wallis constant. -/
theorem tendsto_axisAntiderivative (d : ℕ) :
    Tendsto (axisAntiderivative d) atTop
      (nhds (4 / (Real.pi * (2 * d + 1 : ℕ)))) := by
  have hproduct := (tendsto_natSub_div_nat_one d).mul (tendsto_nat_mul_axisMass d)
  have hscaled := hproduct.const_mul (4 / ((2 * d + 1 : ℕ) : ℝ))
  have heq :
      (fun n : ℕ ↦ 4 / ((2 * d + 1 : ℕ) : ℝ) *
        (((n - d : ℕ) : ℝ) / (n : ℝ) * ((n : ℝ) * axisMass d n))) =ᶠ[atTop]
        axisAntiderivative d := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    unfold axisAntiderivative
    field_simp
  convert hscaled.congr' heq using 1
  all_goals ring_nf

/-- Exact sum of the positive axis-gradient series. -/
theorem tsum_firstGradientTerm_axis (d : ℕ) :
    ∑' n : ℕ, firstGradientTerm d 0 n =
      4 / (Real.pi * (2 * d + 1 : ℕ)) := by
  have hsum := (summable_firstGradientTerm d 0).hasSum.tendsto_sum_nat
  have hsum' : Tendsto (axisAntiderivative d) atTop
      (nhds (∑' n : ℕ, firstGradientTerm d 0 n)) := by
    convert hsum using 1
    funext N
    exact (sum_firstGradientTerm_axis d N).symm
  exact tendsto_nhds_unique hsum' (tendsto_axisAntiderivative d)

/-- Exact adjacent Fourier-potential increment on a coordinate axis. -/
theorem fourierPotential_axis_succ_sub (d : ℕ) :
    fourierPotential (d + 1) 0 - fourierPotential d 0 =
      4 / (Real.pi * (2 * d + 1 : ℕ)) := by
  rw [fourierPotential_succ_sub, tsum_firstGradientTerm_axis]

/-! ## Telescoping along the axis and the exact constant -/

/-- The Fourier-coordinate potential vanishes at the origin. -/
@[simp] theorem fourierPotential_zero_zero : fourierPotential 0 0 = 0 := by
  unfold fourierPotential fourierProductLoss
  simp

/-- Exact closed form for the potential on a diagonal-coordinate axis. -/
theorem fourierPotential_axis_eq (d : ℕ) :
    fourierPotential d 0 = (4 / Real.pi) * oddReciprocalSum d := by
  induction d with
  | zero => simp [oddReciprocalSum]
  | succ d ih =>
      calc
        fourierPotential (d + 1) 0 =
            (fourierPotential (d + 1) 0 - fourierPotential d 0) +
              fourierPotential d 0 := by ring
        _ = 4 / (Real.pi * (2 * d + 1 : ℕ)) +
              (4 / Real.pi) * oddReciprocalSum d := by
            rw [fourierPotential_axis_succ_sub, ih]
        _ = (4 / Real.pi) * oddReciprocalSum (d + 1) := by
            simp only [oddReciprocalSum, Finset.sum_range_succ]
            have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
            have hodd : (2 * (d : ℝ) + 1) ≠ 0 := by positivity
            norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
            field_simp
            ring

/-- The universal additive constant on a diagonal-coordinate axis. -/
noncomputable def cDiag : ℝ :=
  (4 / Real.pi) *
    (Real.log 2 + (1 / 2 : ℝ) * Real.eulerMascheroniConstant)

/-- Explicit `O(1/d)` axis asymptotic, with the exact additive constant. -/
theorem abs_fourierPotential_axis_sub_log_sub_cDiag_le {d : ℕ} (hd : 0 < d) :
    |fourierPotential d 0 - (2 / Real.pi) * Real.log d - cDiag| ≤
      4 / (Real.pi * d) := by
  have hrate := abs_oddReciprocalSum_sub_asymptotic_le hd
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [fourierPotential_axis_eq]
  unfold cDiag
  calc
    |4 / Real.pi * oddReciprocalSum d - 2 / Real.pi * Real.log d -
        4 / Real.pi *
          (Real.log 2 + (1 / 2 : ℝ) * Real.eulerMascheroniConstant)| =
        |4 / Real.pi| *
          |oddReciprocalSum d - (1 / 2 : ℝ) * Real.log d - Real.log 2 -
            (1 / 2 : ℝ) * Real.eulerMascheroniConstant| := by
      rw [← abs_mul]
      congr 1
      field_simp
      ring
    _ = (4 / Real.pi) *
          |oddReciprocalSum d - (1 / 2 : ℝ) * Real.log d - Real.log 2 -
            (1 / 2 : ℝ) * Real.eulerMascheroniConstant| := by
      rw [abs_of_pos (div_pos (by norm_num) hpi)]
    _ ≤ (4 / Real.pi) * (1 / (d : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hrate (div_nonneg (by norm_num) hpi.le)
    _ = 4 / (Real.pi * d) := by ring

end PotentialAxis
end Erdos1165
