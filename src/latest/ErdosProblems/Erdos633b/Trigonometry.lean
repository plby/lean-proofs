import ErdosProblems.Erdos633b.Specification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rational half-angle coordinates

This proves the rationality equivalence needed for cases (4), (5), and (8).
No tiling classification or elliptic-curve statement is assumed.
-/

namespace Erdos633b

theorem cos_ne_neg_one_of_triangle_angle (a : ℝ) (ha : 0 < a) (haπ : a < Real.pi) :
    Real.cos a ≠ -1 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have hsc := Real.sin_sq_add_cos_sq a
  intro h
  rw [h] at hsc
  nlinarith

theorem scaled_tan_half_identity (a : ℝ) (hc : Real.cos a ≠ -1) :
    Real.sqrt 3 * Real.tan (a / 2) =
      (Real.sqrt 3 * Real.sin a) / (1 + Real.cos a) := by
  have hd : 1 + Real.cos a ≠ 0 := by intro h; apply hc; linarith
  apply (eq_div_iff hd).mpr
  rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq a hc,
    Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq]
  field_simp
  ring

theorem groupTwo_cos_coordinate (a : ℝ) (q : ℚ) (hc : Real.cos a ≠ -1)
    (hq : (q : ℝ) = Real.sqrt 3 * Real.tan (a / 2)) :
    Real.cos a = (3 - (q : ℝ) ^ 2) / (3 + (q : ℝ) ^ 2) := by
  have hsq : (q : ℝ) ^ 2 = 3 * Real.tan (a / 2) ^ 2 := by
    rw [hq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have htan : Real.tan (a / 2) ^ 2 = (q : ℝ) ^ 2 / 3 := by linarith
  rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq a hc, htan]
  field_simp

theorem groupTwo_sin_coordinate (a : ℝ) (q : ℚ)
    (hq : (q : ℝ) = Real.sqrt 3 * Real.tan (a / 2)) :
    Real.sqrt 3 * Real.sin a = 6 * (q : ℝ) / (3 + (q : ℝ) ^ 2) := by
  have hsq : (q : ℝ) ^ 2 = 3 * Real.tan (a / 2) ^ 2 := by
    rw [hq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have htan : Real.tan (a / 2) ^ 2 = (q : ℝ) ^ 2 / 3 := by linarith
  rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq, htan,
    ← mul_div_assoc]
  have hnum : Real.sqrt 3 * (2 * Real.tan (a / 2)) = 2 * (q : ℝ) := by
    rw [hq]
    ring
  rw [hnum]
  field_simp
  ring

theorem groupTwo_rationality_iff (a : ℝ) (ha : 0 < a) (haπ : a < Real.pi) :
    IsRational (Real.sqrt 3 * Real.tan (a / 2)) ↔
      IsRational (Real.sqrt 3 * Real.sin a) ∧ IsRational (Real.cos a) := by
  have hc := cos_ne_neg_one_of_triangle_angle a ha haπ
  constructor
  · rintro ⟨q, hq⟩
    constructor
    · refine ⟨6 * q / (3 + q ^ 2), ?_⟩
      push_cast
      exact (groupTwo_sin_coordinate a q hq).symm
    · refine ⟨(3 - q ^ 2) / (3 + q ^ 2), ?_⟩
      push_cast
      exact (groupTwo_cos_coordinate a q hc hq).symm
  · rintro ⟨⟨q, hq⟩, ⟨p, hp⟩⟩
    refine ⟨q / (1 + p), ?_⟩
    push_cast
    rw [hq, hp]
    exact (scaled_tan_half_identity a hc).symm

theorem groupOne_sin_gamma (a : ℝ) :
    Real.sin ((Real.pi + a) / 2) = Real.cos (a / 2) := by
  rw [add_div, Real.sin_add]
  simp

theorem groupOne_sin_beta (a : ℝ) :
    Real.sin ((Real.pi - 3 * a) / 2) =
      Real.cos (a / 2) * (1 - 4 * Real.sin (a / 2) ^ 2) := by
  rw [sub_div, Real.sin_pi_div_two_sub,
    show 3 * a / 2 = 2 * (a / 2) + a / 2 by ring,
    Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination 2 * Real.cos (a / 2) * Real.sin_sq_add_cos_sq (a / 2)

theorem groupOne_sine_ratios (a : ℝ) (ha : 0 < a) (ha3 : a < Real.pi / 3) :
    Real.sin a / Real.sin ((Real.pi + a) / 2) = 2 * Real.sin (a / 2) ∧
    Real.sin ((Real.pi - 3 * a) / 2) / Real.sin ((Real.pi + a) / 2) =
      1 - (2 * Real.sin (a / 2)) ^ 2 := by
  have hc : Real.cos (a / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
    convert Real.sin_two_mul (a / 2) using 1
    congr 1
    ring
  constructor
  · rw [groupOne_sin_gamma, hs]
    field_simp
  · rw [groupOne_sin_beta, groupOne_sin_gamma]
    field_simp
    ring

theorem groupOne_rationality_iff (a : ℝ) (ha : 0 < a) (ha3 : a < Real.pi / 3) :
    (IsRational (Real.sin a / Real.sin ((Real.pi + a) / 2)) ∧
      IsRational (Real.sin ((Real.pi - 3 * a) / 2) / Real.sin ((Real.pi + a) / 2))) ↔
      IsRational (Real.sin (a / 2)) := by
  rw [(groupOne_sine_ratios a ha ha3).1, (groupOne_sine_ratios a ha ha3).2]
  constructor
  · rintro ⟨⟨q, hq⟩, _⟩
    refine ⟨q / 2, ?_⟩
    push_cast
    linarith
  · rintro ⟨q, hq⟩
    constructor
    · refine ⟨2 * q, ?_⟩
      push_cast
      rw [hq]
    · refine ⟨1 - (2 * q) ^ 2, ?_⟩
      push_cast
      rw [hq]

end Erdos633b
