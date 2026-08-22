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

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Moments.Basic

/-!
# Chernoff bounds for a geometric law

This file proves explicit sub-Gaussian moderate-deviation estimates for sums of
independent geometric random variables with success probability `15 / 16`.
Here a geometric variable counts failures before the first success, so its mean
is `1 / 15`.  The proof computes the moment-generating function exactly and
uses only the elementary estimate

`|exp t - 1 - t| ≤ t²` for `|t| ≤ 1`.

The resulting estimates are valid throughout the range `0 ≤ a ≤ i`, and
hence in particular in the moderate-deviation range `sqrt i ≪ a ≪ i`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Erdos1165.GeometricChernoff

/-- The success probability `15 / 16`, as a point of the unit interval. -/
noncomputable def success15 : unitInterval :=
  ⟨15 / 16, by norm_num, by norm_num⟩

/-- The geometric distribution counting failures before a success of probability `15 / 16`. -/
noncomputable def geometric15 : Measure ℕ := geometricMeasure success15

instance : IsProbabilityMeasure geometric15 := by
  unfold geometric15
  infer_instance

lemma success15_ne_zero : success15 ≠ 0 := by
  intro h
  have h' := congrArg ((↑·) : unitInterval → ℝ) h
  norm_num [success15] at h'

lemma geometric15_real_singleton (n : ℕ) :
    geometric15.real {n} = (1 / 16 : ℝ) ^ n * (15 / 16) := by
  rw [geometric15, geometricMeasure_real_singleton success15_ne_zero]
  norm_num [success15]

/-- A geometric variable with success probability `15 / 16` has mean `1 / 15`. -/
lemma geometric15_mean :
    ∫ n : ℕ, (n : ℝ) ∂geometric15 = 1 / 15 := by
  rw [geometric15, integral_geometricMeasure success15_ne_zero]
  simp only [success15, smul_eq_mul]
  have hratio : |(1 / 16 : ℝ)| < 1 := by norm_num
  calc
    ∑' n : ℕ, ((1 - (15 / 16 : ℝ)) ^ n * (15 / 16)) * (n : ℝ) =
        (15 / 16 : ℝ) * ∑' n : ℕ, (n : ℝ) * (1 / 16 : ℝ) ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    _ = (15 / 16 : ℝ) * ((1 / 16 : ℝ) / (1 - 1 / 16) ^ 2) := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one hratio]
    _ = 1 / 15 := by norm_num

/-- Product law of `i` independent geometric variables. -/
noncomputable def geometric15Vector (i : ℕ) : Measure (Fin i → ℕ) :=
  Measure.pi (fun _ ↦ geometric15)

instance (i : ℕ) : IsProbabilityMeasure (geometric15Vector i) := by
  unfold geometric15Vector
  infer_instance

/-- Sum of the coordinates, embedded in the reals. -/
def geometricSum {i : ℕ} (g : Fin i → ℕ) : ℝ :=
  ∑ j, (g j : ℝ)

/-- The centered sum; each summand has mean `1 / 15`. -/
noncomputable def centeredGeometricSum {i : ℕ} (g : Fin i → ℕ) : ℝ :=
  geometricSum g - (i : ℝ) / 15

lemma measurable_geometricSum (i : ℕ) :
    Measurable (@geometricSum i) := by
  fun_prop

lemma measurable_centeredGeometricSum (i : ℕ) :
    Measurable (@centeredGeometricSum i) := by
  fun_prop

/-! ## Elementary exponential estimates -/

lemma exp_le_one_add_add_sq {t : ℝ} (ht : |t| ≤ 1) :
    exp t ≤ 1 + t + t ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le ht
  have h' : exp t - 1 - t ≤ t ^ 2 := (le_abs_self _).trans h
  linarith

lemma exp_neg_le_one_sub_add_sq {t : ℝ} (ht : |t| ≤ 1) :
    exp (-t) ≤ 1 - t + t ^ 2 := by
  have h := exp_le_one_add_add_sq (t := -t) (by simpa using ht)
  convert h using 1
  ring

/-! ## Exact moment-generating function -/

lemma geometric15_integrable_exp (t : ℝ) (ht : exp t < 16) :
    Integrable (fun n : ℕ ↦ exp (t * (n : ℝ))) geometric15 := by
  rw [geometric15, integrable_geometricMeasure_iff success15_ne_zero]
  simp only [Real.norm_eq_abs, abs_exp, success15]
  have hratio : |exp t / 16| < 1 := by
    rw [abs_of_pos (by positivity : 0 < exp t / 16)]
    exact (div_lt_one (by norm_num : (0 : ℝ) < 16)).2 ht
  have hs := (summable_geometric_of_norm_lt_one hratio).mul_right (15 / 16 : ℝ)
  refine hs.congr fun n ↦ ?_
  rw [show t * (n : ℝ) = (n : ℝ) * t by ring]
  rw [exp_nat_mul]
  norm_num
  ring

lemma geometric15_mgf (t : ℝ) (ht : exp t < 16) :
    mgf (fun n : ℕ ↦ (n : ℝ)) geometric15 t = 15 / (16 - exp t) := by
  rw [mgf, geometric15, integral_geometricMeasure success15_ne_zero]
  simp only [success15, smul_eq_mul]
  have hratio : |exp t / 16| < 1 := by
    rw [abs_of_pos (by positivity : 0 < exp t / 16)]
    exact (div_lt_one (by norm_num : (0 : ℝ) < 16)).2 ht
  calc
    ∑' n : ℕ, ((1 - (15 / 16 : ℝ)) ^ n * (15 / 16)) * exp (t * (n : ℝ)) =
        (15 / 16 : ℝ) * ∑' n : ℕ, (exp t / 16) ^ n := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          rw [show t * (n : ℝ) = (n : ℝ) * t by ring]
          rw [exp_nat_mul]
          ring
    _ = (15 / 16 : ℝ) * (1 - exp t / 16)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hratio]
    _ = 15 / (16 - exp t) := by
      field_simp

/-- Exact MGF of one centered geometric variable. -/
lemma centered_geometric15_mgf (t : ℝ) (ht : exp t < 16) :
    mgf (fun n : ℕ ↦ (n : ℝ) - 1 / 15) geometric15 t =
      exp (-t / 15) * (15 / (16 - exp t)) := by
  have hfun : (fun n : ℕ ↦ (n : ℝ) - 1 / 15) =
      fun n : ℕ ↦ (n : ℝ) + (-1 / 15) := by
    funext n
    ring
  rw [hfun, mgf_add_const, geometric15_mgf t ht]
  rw [mul_comm]
  congr 1
  congr 1
  ring

/-- For `0 ≤ t ≤ 1/2`, the MGF of one centered variable is bounded by `exp(t²)`. -/
lemma centered_geometric15_mgf_le_exp_sq {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    mgf (fun n : ℕ ↦ (n : ℝ) - 1 / 15) geometric15 t ≤ exp (t ^ 2) := by
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have hexp : exp t ≤ 1 + t + t ^ 2 := exp_le_one_add_add_sq habs
  have hexp16 : exp t < 16 := lt_of_le_of_lt hexp (by nlinarith [sq_nonneg t])
  rw [centered_geometric15_mgf t hexp16]
  let R : ℝ := 1 + t / 15 + t ^ 2
  have hR : 0 ≤ R := by dsimp [R]; nlinarith [sq_nonneg t]
  have hden : 0 < 16 - exp t := by linarith
  have hpoly : 0 ≤ 209 - 16 * t - 15 * t ^ 2 := by nlinarith [sq_nonneg t]
  have hbase : 15 ≤ R * (15 - t - t ^ 2) := by
    have hmul := mul_nonneg (sq_nonneg t) hpoly
    dsimp [R]
    nlinarith
  have hden_lower : 15 - t - t ^ 2 ≤ 16 - exp t := by linarith
  have hratio : 15 / (16 - exp t) ≤ R := by
    rw [div_le_iff₀ hden]
    exact hbase.trans (mul_le_mul_of_nonneg_left hden_lower hR)
  calc
    exp (-t / 15) * (15 / (16 - exp t)) ≤ exp (-t / 15) * R := by
      exact mul_le_mul_of_nonneg_left hratio (exp_pos _).le
    _ ≤ exp (-t / 15) * exp (t / 15 + t ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by
        dsimp [R]
        have h := Real.add_one_le_exp (t / 15 + t ^ 2)
        ring_nf at h ⊢
        exact h)
        (exp_pos _).le
    _ = exp (t ^ 2) := by
      rw [← exp_add]
      congr 1
      ring

/-- The same MGF estimate at the negative argument `-t`. -/
lemma centered_geometric15_mgf_neg_le_exp_sq {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    mgf (fun n : ℕ ↦ (n : ℝ) - 1 / 15) geometric15 (-t) ≤ exp (t ^ 2) := by
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have hexp : exp (-t) ≤ 1 - t + t ^ 2 := exp_neg_le_one_sub_add_sq habs
  have hexp16 : exp (-t) < 16 := lt_of_le_of_lt hexp (by nlinarith [sq_nonneg t])
  rw [centered_geometric15_mgf (-t) hexp16]
  let R : ℝ := 1 - t / 15 + t ^ 2
  have hR : 0 ≤ R := by dsimp [R]; nlinarith [sq_nonneg t]
  have hden : 0 < 16 - exp (-t) := by linarith
  have hpoly : 0 ≤ 209 + 16 * t - 15 * t ^ 2 := by nlinarith [sq_nonneg t]
  have hbase : 15 ≤ R * (15 + t - t ^ 2) := by
    have hmul := mul_nonneg (sq_nonneg t) hpoly
    dsimp [R]
    nlinarith
  have hden_lower : 15 + t - t ^ 2 ≤ 16 - exp (-t) := by linarith
  have hratio : 15 / (16 - exp (-t)) ≤ R := by
    rw [div_le_iff₀ hden]
    exact hbase.trans (mul_le_mul_of_nonneg_left hden_lower hR)
  calc
    exp (-(-t) / 15) * (15 / (16 - exp (-t))) ≤ exp (t / 15) * R := by
      have heq : exp (-(-t) / 15) = exp (t / 15) := by
        congr 1
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hratio (exp_pos _).le
    _ ≤ exp (t / 15) * exp (-t / 15 + t ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by
        dsimp [R]
        have h := Real.add_one_le_exp (-t / 15 + t ^ 2)
        ring_nf at h ⊢
        exact h)
        (exp_pos _).le
    _ = exp (t ^ 2) := by
      rw [← exp_add]
      congr 1
      ring

/-! ## Sums of independent variables -/

lemma centeredGeometricSum_eq_sum {i : ℕ} (g : Fin i → ℕ) :
    centeredGeometricSum g = ∑ j, ((g j : ℝ) - 1 / 15) := by
  simp [centeredGeometricSum, geometricSum, Finset.sum_sub_distrib, div_eq_mul_inv]

/-- The exact product formula for the MGF of the centered sum. -/
lemma centeredGeometricSum_mgf (i : ℕ) (t : ℝ) :
    mgf (@centeredGeometricSum i) (geometric15Vector i) t =
      mgf (fun n : ℕ ↦ (n : ℝ) - 1 / 15) geometric15 t ^ i := by
  rw [mgf]
  change (∫ g, exp (t * centeredGeometricSum g) ∂(Measure.pi fun _ : Fin i ↦ geometric15)) = _
  simp_rw [centeredGeometricSum_eq_sum, Finset.mul_sum, exp_sum]
  change (∫ g : Fin i → ℕ, ∏ j, exp (t * ((g j : ℝ) - 1 / 15))
      ∂(Measure.pi fun _ : Fin i ↦ geometric15)) =
    (∫ n : ℕ, exp (t * ((n : ℝ) - 1 / 15)) ∂geometric15) ^ i
  simpa using integral_fintype_prod_eq_pow (ι := Fin i) (E := ℕ) (𝕜 := ℝ)
    (mE := inferInstance) (μ := geometric15)
    (fun n : ℕ ↦ exp (t * ((n : ℝ) - 1 / 15)))

/-- The MGF bound for a centered sum at a positive argument. -/
lemma centeredGeometricSum_mgf_le {i : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    mgf (@centeredGeometricSum i) (geometric15Vector i) t ≤
      exp ((i : ℝ) * t ^ 2) := by
  rw [centeredGeometricSum_mgf]
  calc
    mgf (fun n : ℕ ↦ (n : ℝ) - 1 / 15) geometric15 t ^ i ≤
        exp (t ^ 2) ^ i := by
      exact (pow_le_pow_left₀ mgf_nonneg (centered_geometric15_mgf_le_exp_sq ht0 ht)) i
    _ = exp ((i : ℝ) * t ^ 2) := by
      rw [← exp_nat_mul]

/-- The MGF bound for a centered sum at a negative argument. -/
lemma centeredGeometricSum_mgf_neg_le {i : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    mgf (@centeredGeometricSum i) (geometric15Vector i) (-t) ≤
      exp ((i : ℝ) * t ^ 2) := by
  rw [centeredGeometricSum_mgf]
  calc
    mgf (fun n : ℕ ↦ (n : ℝ) - 1 / 15) geometric15 (-t) ^ i ≤
        exp (t ^ 2) ^ i := by
      exact (pow_le_pow_left₀ mgf_nonneg (centered_geometric15_mgf_neg_le_exp_sq ht0 ht)) i
    _ = exp ((i : ℝ) * t ^ 2) := by
      rw [← exp_nat_mul]

lemma integrable_exp_centeredGeometricSum {i : ℕ} {t : ℝ} (ht : exp t < 16) :
    Integrable (fun g ↦ exp (t * centeredGeometricSum g)) (geometric15Vector i) := by
  apply (mgf_pos_iff (X := @centeredGeometricSum i)
    (μ := geometric15Vector i) (t := t)).mp
  rw [centeredGeometricSum_mgf, centered_geometric15_mgf t ht]
  have hden : 0 < 16 - exp t := by linarith
  positivity

/-! ## Chernoff bounds -/

/-- Upper-tail Chernoff bound for the centered sum.  The constant is explicit and
the estimate is uniform for every `0 ≤ a ≤ i`. -/
theorem centeredGeometricSum_upper_tail (i : ℕ) (hi : 0 < i) {a : ℝ}
    (ha0 : 0 ≤ a) (hai : a ≤ i) :
    (geometric15Vector i).real {g | a ≤ centeredGeometricSum g} ≤
      exp (-(a ^ 2) / (4 * (i : ℝ))) := by
  let t : ℝ := a / (2 * (i : ℝ))
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht : t ≤ 1 / 2 := by
    dsimp [t]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * i)]
    nlinarith
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have hexp : exp t < 16 :=
    lt_of_le_of_lt (exp_le_one_add_add_sq habs) (by nlinarith [sq_nonneg t])
  have hchernoff := measure_ge_le_exp_mul_mgf
    (μ := geometric15Vector i) (X := @centeredGeometricSum i) a ht0
    (integrable_exp_centeredGeometricSum hexp)
  calc
    (geometric15Vector i).real {g | a ≤ centeredGeometricSum g} ≤
        exp (-t * a) * mgf (@centeredGeometricSum i) (geometric15Vector i) t := hchernoff
    _ ≤ exp (-t * a) * exp ((i : ℝ) * t ^ 2) := by
      exact mul_le_mul_of_nonneg_left (centeredGeometricSum_mgf_le ht0 ht) (exp_pos _).le
    _ = exp (-(a ^ 2) / (4 * (i : ℝ))) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

/-- Lower-tail Chernoff bound for the centered sum. -/
theorem centeredGeometricSum_lower_tail (i : ℕ) (hi : 0 < i) {a : ℝ}
    (ha0 : 0 ≤ a) (hai : a ≤ i) :
    (geometric15Vector i).real {g | centeredGeometricSum g ≤ -a} ≤
      exp (-(a ^ 2) / (4 * (i : ℝ))) := by
  let t : ℝ := a / (2 * (i : ℝ))
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht : t ≤ 1 / 2 := by
    dsimp [t]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * i)]
    nlinarith
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have hexp : exp (-t) < 16 :=
    lt_of_le_of_lt (exp_neg_le_one_sub_add_sq habs) (by nlinarith [sq_nonneg t])
  have hchernoff := measure_le_le_exp_mul_mgf
    (μ := geometric15Vector i) (X := @centeredGeometricSum i) (-a) (neg_nonpos.mpr ht0)
    (integrable_exp_centeredGeometricSum hexp)
  calc
    (geometric15Vector i).real {g | centeredGeometricSum g ≤ -a} ≤
        exp (-(-t) * (-a)) * mgf (@centeredGeometricSum i) (geometric15Vector i) (-t) := hchernoff
    _ ≤ exp (-(-t) * (-a)) * exp ((i : ℝ) * t ^ 2) := by
      exact mul_le_mul_of_nonneg_left (centeredGeometricSum_mgf_neg_le ht0 ht) (exp_pos _).le
    _ = exp (-(a ^ 2) / (4 * (i : ℝ))) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

/-- Upper tail in terms of the uncentered sum and its mean `i / 15`. -/
theorem geometricSum_upper_tail (i : ℕ) (hi : 0 < i) {a : ℝ}
    (ha0 : 0 ≤ a) (hai : a ≤ i) :
    (geometric15Vector i).real {g | (i : ℝ) / 15 + a ≤ geometricSum g} ≤
      exp (-(a ^ 2) / (4 * (i : ℝ))) := by
  rw [show {g | (i : ℝ) / 15 + a ≤ geometricSum g} =
      {g | a ≤ centeredGeometricSum g} by
    ext g
    simp only [mem_ofPred_eq, centeredGeometricSum]
    constructor <;> intro h <;> linarith]
  exact centeredGeometricSum_upper_tail i hi ha0 hai

/-- Lower tail in terms of the uncentered sum and its mean `i / 15`. -/
theorem geometricSum_lower_tail (i : ℕ) (hi : 0 < i) {a : ℝ}
    (ha0 : 0 ≤ a) (hai : a ≤ i) :
    (geometric15Vector i).real {g | geometricSum g ≤ (i : ℝ) / 15 - a} ≤
      exp (-(a ^ 2) / (4 * (i : ℝ))) := by
  rw [show {g | geometricSum g ≤ (i : ℝ) / 15 - a} =
      {g | centeredGeometricSum g ≤ -a} by
    ext g
    simp only [mem_ofPred_eq, centeredGeometricSum]
    constructor <;> intro h <;> linarith]
  exact centeredGeometricSum_lower_tail i hi ha0 hai

end Erdos1165.GeometricChernoff
