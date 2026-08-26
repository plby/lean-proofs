/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Vanishing Wronskians give constant linear relations in characteristic zero.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.WronskianThree

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma wronskian_common_factor (d p q : K[X]) :
    wronskian (d * p) (d * q) = d ^ 2 * wronskian p q := by
  simp [wronskian, derivative_mul]
  ring

theorem exists_constant_mul_of_wronskian_eq_zero (p q : K[X]) (hp : p ≠ 0)
    (hW : wronskian p q = 0) : ∃ k : K, q = C k * p := by
  classical
  let d := gcd p q
  let u := p / d
  let v := q / d
  have hd : d ≠ 0 := gcd_ne_zero_of_left hp
  have hpu : d * u = p := EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left _ _)
  have hqv : d * v = q := EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right _ _)
  have hu : u ≠ 0 := by intro h; rw [h, mul_zero] at hpu; exact hp hpu.symm
  have hcop : IsCoprime u v := isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hd
  have hWuv : wronskian u v = 0 := by
    have h := wronskian_common_factor d u v
    rw [hpu, hqv, hW] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 hd)
  obtain ⟨hdu, hdv⟩ := hcop.wronskian_eq_zero_iff.mp hWuv
  have huC := eq_C_of_derivative_eq_zero hdu
  have hvC := eq_C_of_derivative_eq_zero hdv
  have hu0 : u.coeff 0 ≠ 0 := by
    intro h
    exact hu (by rw [huC, h, C_0])
  have hvu : v = C (v.coeff 0 / u.coeff 0) * u := by
    rw [huC, coeff_C_zero, ← C_mul, div_mul_cancel₀ _ hu0]
    exact hvC
  refine ⟨v.coeff 0 / u.coeff 0, ?_⟩
  calc
    q = d * v := hqv.symm
    _ = d * (C (v.coeff 0 / u.coeff 0) * u) := congrArg (d * ·) hvu
    _ = C (v.coeff 0 / u.coeff 0) * (d * u) := by ring
    _ = _ := by rw [hpu]

omit [CharZero K] in
lemma wronskian_pair_identity (p q r : K[X]) :
    wronskian (wronskian p q) (wronskian p r) = p * wronskianThree ![p, q, r] := by
  simp [wronskian, wronskianThree, Matrix.det_fin_three]
  ring

/-- No analytic or differential-field result is assumed: polynomial gcds
and the two-column Wronskian criterion give the constant relation. -/
theorem exists_relation_of_wronskianThree_eq_zero (p q r : K[X])
    (hW : wronskianThree ![p, q, r] = 0) :
    ∃ a b c : K, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ C a * p + C b * q + C c * r = 0 := by
  by_cases hp : p = 0
  · exact ⟨1, 0, 0, Or.inl one_ne_zero, by simp [hp]⟩
  by_cases hpq : wronskian p q = 0
  · obtain ⟨k, hk⟩ := exists_constant_mul_of_wronskian_eq_zero p q hp hpq
    refine ⟨-k, 1, 0, Or.inr (Or.inl one_ne_zero), ?_⟩
    simp [hk]
  have hpair : wronskian (wronskian p q) (wronskian p r) = 0 := by
    rw [wronskian_pair_identity, hW, mul_zero]
  obtain ⟨k, hk⟩ := exists_constant_mul_of_wronskian_eq_zero _ _ hpq hpair
  have hWr : wronskian p (r - C k * q) = 0 := by
    have hid : wronskian p (r - C k * q) = wronskian p r - C k * wronskian p q := by
      simp [wronskian]
      ring
    rw [hid, hk, sub_self]
  obtain ⟨l, hl⟩ := exists_constant_mul_of_wronskian_eq_zero p (r - C k * q) hp hWr
  refine ⟨l, k, -1, Or.inr (Or.inr (neg_ne_zero.mpr one_ne_zero)), ?_⟩
  simp only [map_neg, map_one, neg_mul, one_mul]
  linear_combination -hl

omit [CharZero K] in
lemma wronskian_sixth_powers (p q : K[X]) :
    wronskian (p ^ 6) (q ^ 6) = 6 * p ^ 5 * q ^ 5 * wronskian p q := by
  simp only [wronskian, derivative_pow, C_eq_natCast]
  ring

/-- A cancelling pair of sixth powers gives proportional coordinate
polynomials, not merely equality of their sets of roots. -/
theorem exists_constant_mul_of_sixth_cancellation (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p ^ 6 + q ^ 6 = 0) : ∃ k : K, q = C k * p := by
  have hW : wronskian (p ^ 6) (q ^ 6) = 0 := by
    have hqpow : q ^ 6 = -(p ^ 6) := by linear_combination h
    rw [hqpow, wronskian_neg_right, wronskian_self_eq_zero, neg_zero]
  rw [wronskian_sixth_powers] at hW
  have hfactor : (6 : K[X]) * p ^ 5 * q ^ 5 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 5 hp)) (pow_ne_zero 5 hq)
  exact exists_constant_mul_of_wronskian_eq_zero p q hp
    ((mul_eq_zero.mp hW).resolve_left hfactor)

#print axioms exists_relation_of_wronskianThree_eq_zero
-- 'Erdos477.Geometry.exists_relation_of_wronskianThree_eq_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
