import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An elementary mean square bound for the divisor-counting function

The natural-denominator cutoff only needs a polynomial-logarithmic upper
bound for `sum_{n <= X} tau(n)^2`.  This file proves one directly, without an
asymptotic divisor theorem.  The proof expands the two divisor indicators,
counts common multiples by an `lcm`, and bounds the resulting gcd sum by
three harmonic sums.
-/

open Finset
open scoped ArithmeticFunction.sigma BigOperators

namespace Erdos1002

noncomputable section

/-- Positive multiples of `m` not exceeding `X`. -/
def positiveMultiplesIcc (X m : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun n ↦ m ∣ n

/-- Division by a positive `m` identifies its positive multiples up to `X`
with the positive integers up to `X/m`. -/
def positiveMultiplesIccEquiv (X m : ℕ) (hm : 0 < m) :
    {n // n ∈ positiveMultiplesIcc X m} ≃ {k // k ∈ Icc 1 (X / m)} where
  toFun n := by
    refine ⟨(n : ℕ) / m, ?_⟩
    rcases mem_filter.mp n.property with ⟨hnIcc, hmn⟩
    rw [mem_Icc] at hnIcc ⊢
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hmn) hm
    · exact Nat.div_le_div_right hnIcc.2
  invFun k := by
    refine ⟨m * (k : ℕ), ?_⟩
    rw [positiveMultiplesIcc, mem_filter, mem_Icc]
    have hk := k.property
    rw [mem_Icc] at hk
    refine ⟨⟨Nat.mul_pos hm hk.1, ?_⟩, dvd_mul_right m (k : ℕ)⟩
    calc
      m * (k : ℕ) ≤ m * (X / m) := Nat.mul_le_mul_left m hk.2
      _ ≤ X := Nat.mul_div_le X m
  left_inv n := by
    apply Subtype.ext
    rcases mem_filter.mp n.property with ⟨_hnIcc, hmn⟩
    exact Nat.mul_div_cancel' hmn
  right_inv k := by
    apply Subtype.ext
    exact Nat.mul_div_cancel_left (k : ℕ) hm

theorem card_positiveMultiplesIcc (X m : ℕ) (hm : 0 < m) :
    (positiveMultiplesIcc X m).card = X / m := by
  have hcard := Fintype.card_congr (positiveMultiplesIccEquiv X m hm)
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using! hcard

/-- Exact reciprocal sum over positive multiples. -/
theorem sum_recip_positiveMultiplesIcc_eq
    (X m : ℕ) (hm : 0 < m) :
    (∑ n ∈ Icc 1 X, if m ∣ n then (1 / (n : ℝ)) else 0) =
      (1 / (m : ℝ)) *
        ∑ k ∈ Icc 1 (X / m), (1 / (k : ℝ)) := by
  let A : Finset ℕ := positiveMultiplesIcc X m
  let B : Finset ℕ := Icc 1 (X / m)
  let e : {n // n ∈ A} ≃ {k // k ∈ B} :=
    positiveMultiplesIccEquiv X m hm
  have hleft :
      (∑ n ∈ Icc 1 X, if m ∣ n then (1 / (n : ℝ)) else 0) =
        ∑ n ∈ A, (1 / (n : ℝ)) := by
    symm
    simpa only [A, positiveMultiplesIcc] using!
      Finset.sum_filter (s := Icc 1 X) (p := fun n ↦ m ∣ n)
        (f := fun n ↦ (1 / (n : ℝ)))
  rw [hleft]
  calc
    (∑ n ∈ A, (1 / (n : ℝ))) =
        ∑ n : {n // n ∈ A}, (1 / ((n : ℕ) : ℝ)) := by
      exact (Finset.sum_attach A (fun n ↦ (1 / ((n : ℕ) : ℝ)))).symm
    _ = ∑ n : {n // n ∈ A},
          (1 / (m : ℝ)) * (1 / (((e n : {k // k ∈ B}) : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      have hmn : m ∣ (n : ℕ) :=
        (mem_filter.mp (show (n : ℕ) ∈ positiveMultiplesIcc X m by
          simpa only [A] using! n.property)).2
      have hprod : m * ((n : ℕ) / m) = (n : ℕ) := Nat.mul_div_cancel' hmn
      have hprodR : (m : ℝ) * (((n : ℕ) / m : ℕ) : ℝ) =
          ((n : ℕ) : ℝ) := by exact_mod_cast hprod
      change 1 / ((n : ℕ) : ℝ) =
        (1 / (m : ℝ)) * (1 / (((n : ℕ) / m : ℕ) : ℝ))
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hdivPos : 0 < (n : ℕ) / m := by
        rcases mem_filter.mp (show (n : ℕ) ∈ positiveMultiplesIcc X m by
          simpa only [A] using! n.property) with ⟨hnIcc, _⟩
        rw [mem_Icc] at hnIcc
        exact Nat.div_pos
          (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1) hmn) hm
      have hdivR : (((n : ℕ) / m : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast hdivPos.ne'
      rw [← hprodR]
      field_simp
    _ = ∑ k : {k // k ∈ B},
          (1 / (m : ℝ)) * (1 / ((k : ℕ) : ℝ)) := by
      exact e.sum_comp (fun k : {k // k ∈ B} ↦
        (1 / (m : ℝ)) * (1 / ((k : ℕ) : ℝ)))
    _ = ∑ k ∈ B, (1 / (m : ℝ)) * (1 / (k : ℝ)) := by
      exact Finset.sum_attach B
        (fun k ↦ (1 / (m : ℝ)) * (1 / ((k : ℕ) : ℝ)))
    _ = (1 / (m : ℝ)) * ∑ k ∈ B, (1 / (k : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (1 / (m : ℝ)) *
        ∑ k ∈ Icc 1 (X / m), (1 / (k : ℝ)) := by rfl

/-- The reciprocal mass of multiples of `m` is bounded by `H_X/m`. -/
theorem sum_recip_multiples_Icc_le_harmonic
    (X m : ℕ) (hm : 0 < m) :
    (∑ n ∈ Icc 1 X, if m ∣ n then (1 / (n : ℝ)) else 0) ≤
      (1 / (m : ℝ)) * (harmonic X : ℝ) := by
  rw [sum_recip_positiveMultiplesIcc_eq X m hm]
  have hsub : Icc 1 (X / m) ⊆ Icc 1 X := by
    intro k hk
    rw [mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans (Nat.div_le_self X m)⟩
  have hsum :
      (∑ k ∈ Icc 1 (X / m), (1 / (k : ℝ))) ≤
        ∑ k ∈ Icc 1 X, (1 / (k : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _hk _hnot
    positivity
  have hmnonneg : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  calc
    (1 / (m : ℝ)) *
        ∑ k ∈ Icc 1 (X / m), (1 / (k : ℝ)) ≤
        (1 / (m : ℝ)) * ∑ k ∈ Icc 1 X, (1 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hmnonneg
    _ = (1 / (m : ℝ)) * (harmonic X : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]

theorem harmonic_cast_mono {A B : ℕ} (hAB : A ≤ B) :
    (harmonic A : ℝ) ≤ (harmonic B : ℝ) := by
  have hsub : Icc 1 A ⊆ Icc 1 B := by
    intro k hk
    rw [mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hAB⟩
  have hsum :
      (∑ k ∈ Icc 1 A, (1 / (k : ℝ))) ≤
        ∑ k ∈ Icc 1 B, (1 / (k : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _hk _hnot
    positivity
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div] using! hsum

/-! ## Expanding the divisor square -/

theorem divisors_eq_filter_dvd_Icc {n X : ℕ} (hn : n ∈ Icc 1 X) :
    n.divisors = (Icc 1 X).filter fun d ↦ d ∣ n := by
  have hnRange := mem_Icc.mp hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnRange.1
  have hn0 : n ≠ 0 := hnpos.ne'
  ext d
  rw [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hdvd, _⟩
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
    have hdn : d ≤ n := Nat.le_of_dvd hnpos hdvd
    exact ⟨⟨hdpos, hdn.trans hnRange.2⟩, hdvd⟩
  · rintro ⟨_hdRange, hdvd⟩
    exact ⟨hdvd, hn0⟩

/-- At a fixed `1 <= n <= X`, the square of the divisor count is the double
sum of two divisibility indicators over the common ambient interval. -/
theorem divisor_card_sq_eq_double_indicator {n X : ℕ} (hn : n ∈ Icc 1 X) :
    ((n.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
        if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
  have hcard : ((n.divisors.card : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 X, if d ∣ n then (1 : ℝ) else 0 := by
    rw [divisors_eq_filter_dvd_Icc hn]
    calc
      ((((Icc 1 X).filter fun d ↦ d ∣ n).card : ℕ) : ℝ) =
          ∑ _d ∈ (Icc 1 X).filter (fun d ↦ d ∣ n), (1 : ℝ) := by simp
      _ = ∑ d ∈ Icc 1 X, if d ∣ n then (1 : ℝ) else 0 := by
        exact Finset.sum_filter (s := Icc 1 X) (p := fun d ↦ d ∣ n)
          (f := fun _d ↦ (1 : ℝ))
  rw [hcard, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hdn : d ∣ n <;> by_cases hen : e ∣ n <;>
    simp [hdn, hen]

/-- Divisibility by both `d` and `e` is divisibility by their lcm. -/
theorem sum_common_divisor_indicator_eq_quotient
    (X d e : ℕ) (hd : d ∈ Icc 1 X) (he : e ∈ Icc 1 X) :
    (∑ n ∈ Icc 1 X,
      if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0) =
      ((X / Nat.lcm d e : ℕ) : ℝ) := by
  have hdRange := mem_Icc.mp hd
  have heRange := mem_Icc.mp he
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdRange.1
  have hepos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one heRange.1
  have hlcm : 0 < Nat.lcm d e := Nat.lcm_pos
    hdpos hepos
  have hfilter :
      (Icc 1 X).filter (fun n ↦ d ∣ n ∧ e ∣ n) =
        positiveMultiplesIcc X (Nat.lcm d e) := by
    ext n
    simp only [positiveMultiplesIcc, mem_filter]
    constructor
    · rintro ⟨hnRange, hdn, hen⟩
      exact ⟨hnRange, Nat.lcm_dvd hdn hen⟩
    · rintro ⟨hnRange, hlcmn⟩
      exact ⟨hnRange,
        (Nat.dvd_lcm_left d e).trans hlcmn,
        (Nat.dvd_lcm_right d e).trans hlcmn⟩
  calc
    (∑ n ∈ Icc 1 X,
        if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0) =
        ∑ _n ∈ (Icc 1 X).filter (fun n ↦ d ∣ n ∧ e ∣ n),
          (1 : ℝ) := by
      symm
      exact Finset.sum_filter (s := Icc 1 X)
        (p := fun n ↦ d ∣ n ∧ e ∣ n) (f := fun _n ↦ (1 : ℝ))
    _ = (((Icc 1 X).filter (fun n ↦ d ∣ n ∧ e ∣ n)).card : ℝ) := by
      simp
    _ = ((positiveMultiplesIcc X (Nat.lcm d e)).card : ℝ) := by rw [hfilter]
    _ = ((X / Nat.lcm d e : ℕ) : ℝ) := by
      rw [card_positiveMultiplesIcc X (Nat.lcm d e) hlcm]

/-- Exact finite lcm expansion of the divisor-square mean. -/
theorem sum_divisor_card_sq_eq_lcm_sum (X : ℕ) :
    (∑ n ∈ Icc 1 X, ((n.divisors.card : ℕ) : ℝ) ^ 2) =
      ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
        ((X / Nat.lcm d e : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Icc 1 X, ((n.divisors.card : ℕ) : ℝ) ^ 2) =
        ∑ n ∈ Icc 1 X, ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
          if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact divisor_card_sq_eq_double_indicator hn
    _ = ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X, ∑ n ∈ Icc 1 X,
          if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
          ((X / Nat.lcm d e : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      exact sum_common_divisor_indicator_eq_quotient X d e hd he

/-! ## Bounding the lcm sum by three harmonic sums -/

theorem cast_div_lcm_le_gcd_fraction
    (X d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ((X / Nat.lcm d e : ℕ) : ℝ) ≤
      (X : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hlcm : 0 < Nat.lcm d e := Nat.lcm_pos hd he
  have hde : (d : ℝ) * (e : ℝ) =
      (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) := by
    exact_mod_cast (Nat.gcd_mul_lcm d e).symm
  calc
    ((X / Nat.lcm d e : ℕ) : ℝ) ≤
        (X : ℝ) / (Nat.lcm d e : ℝ) := Nat.cast_div_le
    _ = (X : ℝ) * (Nat.gcd d e : ℝ) /
        ((d : ℝ) * (e : ℝ)) := by
      rw [hde]
      have hgcd : (0 : ℝ) < (Nat.gcd d e : ℝ) := by positivity
      have hlcmR : (0 : ℝ) < (Nat.lcm d e : ℝ) := by exact_mod_cast hlcm
      field_simp

/-- The gcd term is one of the nonnegative common-divisor terms. -/
theorem gcd_fraction_le_sum_common_divisors
    (X d e : ℕ) (hd : d ∈ Icc 1 X) (he : e ∈ Icc 1 X) :
    (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) ≤
      ∑ g ∈ Icc 1 X,
        if g ∣ d ∧ g ∣ e then
          (g : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 := by
  have hdRange := mem_Icc.mp hd
  have heRange := mem_Icc.mp he
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdRange.1
  have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hdpos
  have hgle : Nat.gcd d e ≤ X :=
    (Nat.gcd_le_left e hdpos).trans hdRange.2
  have hgmem : Nat.gcd d e ∈ Icc 1 X := mem_Icc.mpr ⟨hgpos, hgle⟩
  have hnonneg (g : ℕ) (hg : g ∈ Icc 1 X) :
      0 ≤ if g ∣ d ∧ g ∣ e then
        (g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
    split_ifs <;> positivity
  have hsingle := Finset.single_le_sum
    (f := fun g : ℕ ↦ if g ∣ d ∧ g ∣ e then
      (g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)
    hnonneg hgmem
  simpa only [Nat.gcd_dvd_left, Nat.gcd_dvd_right, and_self,
    if_true] using! hsingle

theorem commonDivisorKernel_factor (d e g : ℕ) :
    (if g ∣ d ∧ g ∣ e then
        (g : ℝ) / ((d : ℝ) * (e : ℝ))
      else 0) =
      (g : ℝ) * (if g ∣ d then 1 / (d : ℝ) else 0) *
        (if g ∣ e then 1 / (e : ℝ) else 0) := by
  by_cases hgd : g ∣ d
  · by_cases hge : g ∣ e
    · simp [hgd, hge]
      ring
    · simp [hgd, hge]
  · by_cases hge : g ∣ e <;> simp [hgd, hge]

/-- The complete common-divisor majorant factors into weighted sums of
multiples. -/
theorem sum_commonDivisorKernel_eq (X : ℕ) :
    (∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X, ∑ g ∈ Icc 1 X,
      if g ∣ d ∧ g ∣ e then
        (g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
      ∑ g ∈ Icc 1 X, (g : ℝ) *
        (∑ d ∈ Icc 1 X, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 := by
  let R : Finset ℕ := Icc 1 X
  calc
    (∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X, ∑ g ∈ Icc 1 X,
        if g ∣ d ∧ g ∣ e then
          (g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
        ∑ d ∈ R, ∑ e ∈ R, ∑ g ∈ R,
          (g : ℝ) * (if g ∣ d then 1 / (d : ℝ) else 0) *
            (if g ∣ e then 1 / (e : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      apply Finset.sum_congr rfl
      intro g _hg
      exact commonDivisorKernel_factor d e g
    _ = ∑ d ∈ R, ∑ g ∈ R, ∑ e ∈ R,
          (g : ℝ) * (if g ∣ d then 1 / (d : ℝ) else 0) *
            (if g ∣ e then 1 / (e : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact Finset.sum_comm
    _ = ∑ g ∈ R, ∑ d ∈ R, ∑ e ∈ R,
          (g : ℝ) * (if g ∣ d then 1 / (d : ℝ) else 0) *
            (if g ∣ e then 1 / (e : ℝ) else 0) := by
      exact Finset.sum_comm
    _ = ∑ g ∈ R, (g : ℝ) *
          (∑ d ∈ R, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _hg
      let A : ℕ → ℝ := fun d ↦ if g ∣ d then 1 / (d : ℝ) else 0
      calc
        (∑ d ∈ R, ∑ e ∈ R, (g : ℝ) * A d * A e) =
            ∑ d ∈ R, ((g : ℝ) * A d) * (∑ e ∈ R, A e) := by
          apply Finset.sum_congr rfl
          intro d _hd
          rw [Finset.mul_sum]
        _ = (∑ d ∈ R, (g : ℝ) * A d) * (∑ e ∈ R, A e) := by
          rw [Finset.sum_mul]
        _ = ((g : ℝ) * ∑ d ∈ R, A d) * (∑ e ∈ R, A e) := by
          have hfactor : (∑ d ∈ R, (g : ℝ) * A d) =
              (g : ℝ) * ∑ d ∈ R, A d := by
            rw [Finset.mul_sum]
          rw [hfactor]
        _ = (g : ℝ) * (∑ d ∈ R, A d) ^ 2 := by ring
        _ = (g : ℝ) *
            (∑ d ∈ R, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 := by rfl
    _ = ∑ g ∈ Icc 1 X, (g : ℝ) *
          (∑ d ∈ Icc 1 X, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 := by
      rfl

/-- The gcd double sum is at most `H_X^3`. -/
theorem sum_gcd_fraction_le_harmonic_cube (X : ℕ) :
    (∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
      (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ))) ≤
      (harmonic X : ℝ) ^ 3 := by
  let H : ℝ := (harmonic X : ℝ)
  have hH : 0 ≤ H := by
    dsimp [H]
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    positivity
  calc
    (∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
        (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ))) ≤
        ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X, ∑ g ∈ Icc 1 X,
          if g ∣ d ∧ g ∣ e then
            (g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact gcd_fraction_le_sum_common_divisors X d e hd he
    _ = ∑ g ∈ Icc 1 X, (g : ℝ) *
          (∑ d ∈ Icc 1 X, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 :=
      sum_commonDivisorKernel_eq X
    _ ≤ ∑ g ∈ Icc 1 X, (1 / (g : ℝ)) * H ^ 2 := by
      apply Finset.sum_le_sum
      intro g hg
      have hgRange := mem_Icc.mp hg
      have hgpos : 0 < g := lt_of_lt_of_le Nat.zero_lt_one hgRange.1
      have hmass := sum_recip_multiples_Icc_le_harmonic X g hgpos
      have hmassNonneg : 0 ≤
          ∑ d ∈ Icc 1 X, if g ∣ d then 1 / (d : ℝ) else 0 := by
        apply Finset.sum_nonneg
        intro d _hd
        split_ifs <;> positivity
      calc
        (g : ℝ) *
            (∑ d ∈ Icc 1 X, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 ≤
            (g : ℝ) * ((1 / (g : ℝ)) * H) ^ 2 := by
          gcongr
        _ = (1 / (g : ℝ)) * H ^ 2 := by
          have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
          field_simp
    _ = H ^ 3 := by
      calc
        (∑ g ∈ Icc 1 X, (1 / (g : ℝ)) * H ^ 2) =
            (∑ g ∈ Icc 1 X, (1 / (g : ℝ))) * H ^ 2 := by
          rw [Finset.sum_mul]
        _ = H * H ^ 2 := by
          congr 1
          dsimp [H]
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
            Rat.cast_natCast, one_div]
        _ = H ^ 3 := by ring
    _ = (harmonic X : ℝ) ^ 3 := by rfl

/-- Self-contained divisor-square mean bound with an explicit constant one. -/
theorem sum_divisor_card_sq_le_harmonic_cube (X : ℕ) :
    (∑ n ∈ Icc 1 X, ((n.divisors.card : ℕ) : ℝ) ^ 2) ≤
      (X : ℝ) * (harmonic X : ℝ) ^ 3 := by
  rw [sum_divisor_card_sq_eq_lcm_sum]
  calc
    (∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
        ((X / Nat.lcm d e : ℕ) : ℝ)) ≤
        ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
          (X : ℝ) * (Nat.gcd d e : ℝ) /
            ((d : ℝ) * (e : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact cast_div_lcm_le_gcd_fraction X d e
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1)
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp he).1)
    _ = (X : ℝ) * ∑ d ∈ Icc 1 X, ∑ e ∈ Icc 1 X,
          (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring
    _ ≤ (X : ℝ) * (harmonic X : ℝ) ^ 3 := by
      gcongr
      exact sum_gcd_fraction_le_harmonic_cube X

/-! ## A dyadic average for `sigma_1` -/

/-- The elementary average-order upper bound
`sum_{p <= X} sigma_1(p) <= X^2`. -/
theorem sum_sigma_one_Icc_le_square (X : ℕ) :
    (∑ p ∈ Icc 1 X, (ArithmeticFunction.sigma 1 p : ℝ)) ≤
      (X : ℝ) ^ 2 := by
  calc
    (∑ p ∈ Icc 1 X, (ArithmeticFunction.sigma 1 p : ℝ)) =
        ∑ p ∈ Icc 1 X, ∑ d ∈ Icc 1 X,
          if d ∣ p then (d : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.sigma_one_apply]
      rw [divisors_eq_filter_dvd_Icc hp]
      calc
        ((∑ d ∈ (Icc 1 X).filter (fun d ↦ d ∣ p), d : ℕ) : ℝ) =
            ∑ d ∈ (Icc 1 X).filter (fun d ↦ d ∣ p), (d : ℝ) := by
          exact Nat.cast_sum _ _
        _ = ∑ d ∈ Icc 1 X, if d ∣ p then (d : ℝ) else 0 := by
          exact Finset.sum_filter (s := Icc 1 X) (p := fun d ↦ d ∣ p)
            (f := fun d ↦ (d : ℝ))
    _ = ∑ d ∈ Icc 1 X, ∑ p ∈ Icc 1 X,
          if d ∣ p then (d : ℝ) else 0 := by
      exact Finset.sum_comm
    _ = ∑ d ∈ Icc 1 X,
          (d : ℝ) * ((positiveMultiplesIcc X d).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ p ∈ Icc 1 X, if d ∣ p then (d : ℝ) else 0) =
            ∑ _p ∈ positiveMultiplesIcc X d, (d : ℝ) := by
          symm
          simpa only [positiveMultiplesIcc] using!
            Finset.sum_filter (s := Icc 1 X) (p := fun p ↦ d ∣ p)
              (f := fun _p ↦ (d : ℝ))
        _ = (d : ℝ) * ((positiveMultiplesIcc X d).card : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
          ring
    _ = ∑ d ∈ Icc 1 X, (d : ℝ) * ((X / d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [card_positiveMultiplesIcc X d
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1)]
    _ ≤ ∑ _d ∈ Icc 1 X, (X : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d :=
        lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1
      have hnat : d * (X / d) ≤ X := Nat.mul_div_le X d
      exact_mod_cast hnat
    _ = ((Icc 1 X).card : ℝ) * (X : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
    _ = (X : ℝ) ^ 2 := by
      simp only [Nat.card_Icc, Nat.add_sub_cancel]
      ring

/-- On the exact block `Q < p <= 2Q`, the weighted sigma mass is at most
four. -/
theorem sum_sigma_one_div_sq_Ioc_le_four (Q : ℕ) (hQ : 0 < Q) :
    (∑ p ∈ Ioc Q (2 * Q),
      (ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2) ≤ 4 := by
  have hsubset : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := by
    intro p hp
    rw [mem_Ioc] at hp
    rw [mem_Icc]
    exact ⟨by omega, hp.2⟩
  have hsumSigma :
      (∑ p ∈ Ioc Q (2 * Q), (ArithmeticFunction.sigma 1 p : ℝ)) ≤
        ((2 * Q : ℕ) : ℝ) ^ 2 := by
    calc
      (∑ p ∈ Ioc Q (2 * Q), (ArithmeticFunction.sigma 1 p : ℝ)) ≤
          ∑ p ∈ Icc 1 (2 * Q), (ArithmeticFunction.sigma 1 p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro p _hp _hnot
        positivity
      _ ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := sum_sigma_one_Icc_le_square (2 * Q)
  have hQReal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  calc
    (∑ p ∈ Ioc Q (2 * Q),
        (ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ Ioc Q (2 * Q),
          (ArithmeticFunction.sigma 1 p : ℝ) / (Q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hQp : (Q : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (mem_Ioc.mp hp).1.le
      have hsq : (Q : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by nlinarith
      have hsigmaNonneg : 0 ≤ (ArithmeticFunction.sigma 1 p : ℝ) := by positivity
      exact div_le_div_of_nonneg_left hsigmaNonneg (sq_pos_of_pos hQReal) hsq
    _ = (∑ p ∈ Ioc Q (2 * Q),
          (ArithmeticFunction.sigma 1 p : ℝ)) / (Q : ℝ) ^ 2 := by
      rw [Finset.sum_div]
    _ ≤ (((2 * Q : ℕ) : ℝ) ^ 2) / (Q : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hsumSigma (sq_nonneg (Q : ℝ))
    _ = 4 := by
      push_cast
      field_simp
      norm_num

end

end Erdos1002
