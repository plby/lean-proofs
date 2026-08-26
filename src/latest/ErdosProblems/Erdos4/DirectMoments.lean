import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Direct moment inequalities for the large-gap covering argument

These finite inequalities include the zero-mass cases. They do not assume
prime distribution or the existence of sieve weights with prescribed moments.
-/

open scoped BigOperators

namespace Erdos4.DirectMoments

variable {ι : Type*}

/-- Weighted Cauchy--Schwarz with a possibly zero denominator. -/
theorem weighted_sq_sum_le (s : Finset ι) (w z d : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hd : ∀ i ∈ s, 0 ≤ d i)
    (hz : ∀ i ∈ s, d i = 0 → z i = 0) :
    (∑ i ∈ s, w i * z i) ^ 2 ≤
      (∑ i ∈ s, w i * (z i ^ 2 / d i)) * ∑ i ∈ s, w i * d i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (hw i hi) (div_nonneg (sq_nonneg _) (hd i hi))
  · intro i hi
    exact mul_nonneg (hw i hi) (hd i hi)
  · intro i hi
    by_cases hdi : d i = 0
    · simp [hdi, hz i hi hdi]
    · have heq : (w i * z i) ^ 2 =
          (w i * (z i ^ 2 / d i)) * (w i * d i) := by
        field_simp
      exact heq.le

/-- A finite collection of independent choices misses with probability at
most the reciprocal of one plus its total hitting mass. -/
theorem prod_one_sub_le_inv_one_add_sum (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    ∏ i ∈ s, (1 - a i) ≤ 1 / (1 + ∑ i ∈ s, a i) := by
  classical
  have hmul : (∏ i ∈ s, (1 - a i)) * (1 + ∑ i ∈ s, a i) ≤ 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
      have ha0s : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha0 i (by simp [hi])
      have ha1s : ∀ i ∈ s, a i ≤ 1 := fun i hi => ha1 i (by simp [hi])
      have hprev := ih ha0s ha1s
      have haj0 := ha0 j (by simp)
      have haj1 := ha1 j (by simp)
      have hsum : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha0s
      have hprod : 0 ≤ ∏ i ∈ s, (1 - a i) :=
        Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (ha1s i hi))
      have hlocal : (1 - a j) * (1 + (a j + ∑ i ∈ s, a i)) ≤
          1 + ∑ i ∈ s, a i := by
        nlinarith [mul_nonneg haj0 hsum, sq_nonneg (a j)]
      have hstep := mul_le_mul_of_nonneg_left hlocal hprod
      rw [Finset.prod_insert hjs, Finset.sum_insert hjs]
      nlinarith
  have hden : 0 < 1 + ∑ i ∈ s, a i :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg ha0)
  exact (le_div_iff₀ hden).mpr hmul

/-- The first Cauchy--Schwarz step for normalized tuple choices. -/
theorem sum_sq_le_exposure_mul_mixed (s : Finset ι) (x z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hzx : ∀ i ∈ s, z i ≤ x i) :
    (∑ i ∈ s, z i) ^ 2 ≤
      (∑ i ∈ s, z i / x i) * ∑ i ∈ s, x i * z i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact div_nonneg (hz i hi) (hx i hi)
  · intro i hi
    exact mul_nonneg (hx i hi) (hz i hi)
  · intro i hi
    by_cases hxi : x i = 0
    · have hzi : z i = 0 := le_antisymm (hxi ▸ hzx i hi) (hz i hi)
      simp [hxi, hzi]
    · have heq : z i ^ 2 = (z i / x i) * (x i * z i) := by
        field_simp
      exact heq.le

/-- The pointwise coverage estimate, before averaging over the preliminary
random sieve. A zero normalizing mass contributes a zero hitting mass. -/
theorem coverage_ge_ratio (s : Finset ι) (x z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hzx : ∀ i ∈ s, z i ≤ x i) :
    (∑ i ∈ s, z i) ^ 2 /
        ((∑ i ∈ s, z i) ^ 2 + ∑ i ∈ s, x i * z i) ≤
      1 - ∏ i ∈ s, (1 - z i / x i) := by
  have ha0 : ∀ i ∈ s, 0 ≤ z i / x i :=
    fun i hi => div_nonneg (hz i hi) (hx i hi)
  have ha1 : ∀ i ∈ s, z i / x i ≤ 1 := by
    intro i hi
    by_cases hxi : x i = 0
    · simp [hxi]
    · exact (div_le_one (lt_of_le_of_ne (hx i hi) (Ne.symm hxi))).mpr (hzx i hi)
  have hmiss := prod_one_sub_le_inv_one_add_sum s (fun i => z i / x i) ha0 ha1
  have hcs := sum_sq_le_exposure_mul_mixed s x z hx hz hzx
  have hH : 0 ≤ ∑ i ∈ s, x i * z i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hx i hi) (hz i hi))
  have ht : 0 ≤ ∑ i ∈ s, z i / x i := Finset.sum_nonneg ha0
  have hprod : ∏ i ∈ s, (1 - z i / x i) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i hi
      exact sub_nonneg.mpr (ha1 i hi)
    · intro i hi
      linarith [ha0 i hi]
  by_cases hH0 : ∑ i ∈ s, x i * z i = 0
  · have hZ0 : (∑ i ∈ s, z i) ^ 2 = 0 := by nlinarith [sq_nonneg (∑ i ∈ s, z i)]
    simp only [hZ0, hH0, zero_add, div_zero]
    linarith
  · have hHpos : 0 < ∑ i ∈ s, x i * z i := lt_of_le_of_ne hH (Ne.symm hH0)
    have hd : 0 < (∑ i ∈ s, z i) ^ 2 + ∑ i ∈ s, x i * z i :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) hHpos
    have hratio : 1 / (1 + ∑ i ∈ s, z i / x i) ≤
        (∑ i ∈ s, x i * z i) /
          ((∑ i ∈ s, z i) ^ 2 + ∑ i ∈ s, x i * z i) := by
      apply (div_le_div_iff₀ (by linarith : 0 < 1 + ∑ i ∈ s, z i / x i) hd).mpr
      nlinarith
    have hm := hmiss.trans hratio
    have heq : (∑ i ∈ s, z i) ^ 2 /
          ((∑ i ∈ s, z i) ^ 2 + ∑ i ∈ s, x i * z i) +
        (∑ i ∈ s, x i * z i) /
          ((∑ i ∈ s, z i) ^ 2 + ∑ i ∈ s, x i * z i) = 1 := by
      rw [← add_div, div_self hd.ne']
    linarith

/-- The second Cauchy--Schwarz step. This form needs neither a positive
denominator at every outcome nor an upper bound for the first moment. -/
theorem ratio_of_moments_le_mean_ratio (s : Finset ι) (w z h : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hh : ∀ i ∈ s, 0 ≤ h i) :
    (∑ i ∈ s, w i * z i) ^ 2 /
        (∑ i ∈ s, w i * (z i ^ 2 + h i)) ≤
      ∑ i ∈ s, w i * (z i ^ 2 / (z i ^ 2 + h i)) := by
  have hd : ∀ i ∈ s, 0 ≤ z i ^ 2 + h i :=
    fun i hi => add_nonneg (sq_nonneg _) (hh i hi)
  have hz : ∀ i ∈ s, z i ^ 2 + h i = 0 → z i = 0 := by
    intro i hi heq
    have hzi : z i ^ 2 = 0 := by nlinarith [sq_nonneg (z i), hh i hi]
    exact sq_eq_zero_iff.mp hzi
  have hcs := weighted_sq_sum_le s w z (fun i => z i ^ 2 + h i) hw hd hz
  apply div_le_of_le_mul₀
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hd i hi))
  · exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (hw i hi) (div_nonneg (sq_nonneg _) (hd i hi)))
  · exact hcs

/-- The complete finite direct-moment estimate. The outer weights describe
the preliminary random sieve, and the inner arrays describe source choices. -/
theorem mean_miss_le_moment_ratio {Ω : Type*} (outcomes : Finset Ω)
    (sources : Finset ι) (w : Ω → ℝ) (x z : Ω → ι → ℝ)
    (hw : ∀ o ∈ outcomes, 0 ≤ w o) (hw1 : ∑ o ∈ outcomes, w o = 1)
    (hx : ∀ o ∈ outcomes, ∀ i ∈ sources, 0 ≤ x o i)
    (hz : ∀ o ∈ outcomes, ∀ i ∈ sources, 0 ≤ z o i)
    (hzx : ∀ o ∈ outcomes, ∀ i ∈ sources, z o i ≤ x o i) :
    (∑ o ∈ outcomes, w o * ∏ i ∈ sources, (1 - z o i / x o i)) ≤
      1 - (∑ o ∈ outcomes, w o * ∑ i ∈ sources, z o i) ^ 2 /
        (∑ o ∈ outcomes, w o *
          ((∑ i ∈ sources, z o i) ^ 2 + ∑ i ∈ sources, x o i * z o i)) := by
  have havg := ratio_of_moments_le_mean_ratio outcomes w
    (fun o => ∑ i ∈ sources, z o i)
    (fun o => ∑ i ∈ sources, x o i * z o i) hw
    (fun o ho => Finset.sum_nonneg (fun i hi => mul_nonneg (hx o ho i hi) (hz o ho i hi)))
  have hpoint := Finset.sum_le_sum (s := outcomes) (fun o ho =>
    mul_le_mul_of_nonneg_left (coverage_ge_ratio sources (x o) (z o)
      (hx o ho) (hz o ho) (hzx o ho)) (hw o ho))
  have hsum : (∑ o ∈ outcomes, w o *
      (1 - ∏ i ∈ sources, (1 - z o i / x o i))) =
      1 - ∑ o ∈ outcomes, w o * ∏ i ∈ sources, (1 - z o i / x o i) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hw1]
  rw [hsum] at hpoint
  linarith

end Erdos4.DirectMoments
