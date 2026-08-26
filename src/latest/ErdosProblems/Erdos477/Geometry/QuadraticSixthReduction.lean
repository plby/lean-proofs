/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The exact sixth-power remainder modulo a monic quadratic.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

variable {R : Type*} [CommRing R]

def quadraticSixthLinear (b c : R) : R := -b * (b ^ 2 - c) * (b ^ 2 - 3 * c)

def quadraticSixthConstant (b c : R) : R := -b ^ 4 * c + 3 * b ^ 2 * c ^ 2 - c ^ 3

def quadraticSixthQuotient (b c y : R) : R :=
  y ^ 4 - b * y ^ 3 + (b ^ 2 - c) * y ^ 2 + (-b ^ 3 + 2 * b * c) * y +
    (b ^ 4 - 3 * b ^ 2 * c + c ^ 2)

theorem quadratic_sixth_identity (b c y : R) :
    y ^ 6 = (y ^ 2 + b * y + c) * quadraticSixthQuotient b c y +
      quadraticSixthLinear b c * y + quadraticSixthConstant b c := by
  dsimp only [quadraticSixthQuotient, quadraticSixthLinear, quadraticSixthConstant]
  ring

theorem sixth_eq_quadratic_remainder (b c y : R) (hy : y ^ 2 + b * y + c = 0) :
    y ^ 6 = quadraticSixthLinear b c * y + quadraticSixthConstant b c := by
  rw [quadratic_sixth_identity b c y, hy, zero_mul, zero_add]

lemma quadraticSixthLinear_eq_zero_iff [NoZeroDivisors R] (b c : R) :
    quadraticSixthLinear b c = 0 ↔ b = 0 ∨ b ^ 2 = c ∨ b ^ 2 = 3 * c := by
  simp only [quadraticSixthLinear, mul_eq_zero, neg_eq_zero, sub_eq_zero]
  tauto

open Polynomial

lemma quadratic_dvd_sixth_sub_remainder (b c : R) :
    X ^ 2 + C b * X + C c ∣
      X ^ 6 - (C (quadraticSixthLinear b c) * X + C (quadraticSixthConstant b c)) := by
  refine ⟨quadraticSixthQuotient (C b) (C c) X, ?_⟩
  have h := quadratic_sixth_identity (C b) (C c) (X : R[X])
  have hA : quadraticSixthLinear (C b) (C c) = C (quadraticSixthLinear b c) := by
    simp [quadraticSixthLinear, Polynomial.C_ofNat]
  have hB : quadraticSixthConstant (C b) (C c) = C (quadraticSixthConstant b c) := by
    simp [quadraticSixthConstant, Polynomial.C_ofNat]
  rw [hA, hB] at h
  linear_combination h

lemma quadraticSixthLinear_zero (c : R) : quadraticSixthLinear 0 c = 0 := by
  simp [quadraticSixthLinear]

lemma quadraticSixthConstant_zero (c : R) : quadraticSixthConstant 0 c = -c ^ 3 := by
  simp [quadraticSixthConstant]

def quadraticSixthHomogeneousQuotient (b c n d : R) : R :=
  n ^ 4 - b * n ^ 3 * d + (b ^ 2 - c) * n ^ 2 * d ^ 2 +
    (-b ^ 3 + 2 * b * c) * n * d ^ 3 + (b ^ 4 - 3 * b ^ 2 * c + c ^ 2) * d ^ 4

theorem quadratic_sixth_homogeneous_identity (b c n d : R) :
    n ^ 6 = (n ^ 2 + b * n * d + c * d ^ 2) * quadraticSixthHomogeneousQuotient b c n d +
      quadraticSixthLinear b c * n * d ^ 5 + quadraticSixthConstant b c * d ^ 6 := by
  dsimp only [quadraticSixthHomogeneousQuotient, quadraticSixthLinear, quadraticSixthConstant]
  ring

theorem quadratic_remainder_certificate (b c n d t x k : R)
    (hd : d = quadraticSixthLinear b c)
    (hn : n + quadraticSixthConstant b c + t ^ 6 - x ^ 6 - k = 0) :
    n ^ 6 + (t * d) ^ 6 - x ^ 6 * d ^ 6 - k * d ^ 6 =
      (n ^ 2 + b * n * d + c * d ^ 2) * quadraticSixthHomogeneousQuotient b c n d := by
  have h := quadratic_sixth_homogeneous_identity b c n d
  rw [← hd] at h
  linear_combination h + d ^ 6 * hn

#print axioms sixth_eq_quadratic_remainder
-- 'Erdos477.Geometry.sixth_eq_quadratic_remainder' depends on axioms:
-- [propext, Quot.sound]

#print axioms quadratic_remainder_certificate
-- 'Erdos477.Geometry.quadratic_remainder_certificate' depends on axioms:
-- [propext, Quot.sound]

end Erdos477.Geometry
