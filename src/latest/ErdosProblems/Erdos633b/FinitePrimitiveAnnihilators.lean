import ErdosProblems.Erdos633b.PrimitiveFinitePolynomials
import ErdosProblems.Erdos633b.Boundary48Exclusion

/-! Nine explicit annihilators for the final finite angle pairs.
Every root identity is justified by ring expansion and primitive nonvanishing. -/

namespace Erdos633b
open Polynomial

noncomputable def root28Polynomial : ℚ[X] :=
  X ^ 12 - X ^ 10 + X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1

theorem root28Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 28) :
    aeval z root28Polynomial = 0 := by
  have h14 : z ^ 14 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h4 : z ^ 4 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 28 - 1) * (z ^ 2 - 1) =
      (z ^ 12 - z ^ 10 + z ^ 8 - z ^ 6 + z ^ 4 - z ^ 2 + 1) * ((z ^ 14 - 1) * (z ^ 4 - 1)) := by
        ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h14 h4)
  simpa only [root28Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root28_totient : Nat.totient 28 = 12 := by decide

noncomputable def root36Polynomial : ℚ[X] :=
  X ^ 12 - X ^ 6 + 1

theorem root36Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 36) :
    aeval z root36Polynomial = 0 := by
  have h18 : z ^ 18 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h12 : z ^ 12 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 36 - 1) * (z ^ 6 - 1) =
      (z ^ 12 - z ^ 6 + 1) * ((z ^ 18 - 1) * (z ^ 12 - 1)) := by ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h18 h12)
  simpa only [root36Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root36_totient : Nat.totient 36 = 12 := by decide

noncomputable def root40Polynomial : ℚ[X] :=
  X ^ 16 - X ^ 12 + X ^ 8 - X ^ 4 + 1

theorem root40Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 40) :
    aeval z root40Polynomial = 0 := by
  have h20 : z ^ 20 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h8 : z ^ 8 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 40 - 1) * (z ^ 4 - 1) =
      (z ^ 16 - z ^ 12 + z ^ 8 - z ^ 4 + 1) * ((z ^ 20 - 1) * (z ^ 8 - 1)) := by ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h20 h8)
  simpa only [root40Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root40_totient : Nat.totient 40 = 16 := by decide

noncomputable def root42Polynomial : ℚ[X] :=
  X ^ 12 + X ^ 11 - X ^ 9 - X ^ 8 + X ^ 6 - X ^ 4 - X ^ 3 + X + 1

theorem root42Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 42) :
    aeval z root42Polynomial = 0 := by
  have h21 : z ^ 21 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h14 : z ^ 14 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h6 : z ^ 6 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h1 : z ^ 1 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 42 - 1) * (z ^ 7 - 1) * (z ^ 3 - 1) * (z ^ 2 - 1) =
      (z ^ 12 + z ^ 11 - z ^ 9 - z ^ 8 + z ^ 6 - z ^ 4 - z ^ 3 + z + 1) * ((z ^ 21 - 1) * (z ^ 14
        - 1) * (z ^ 6 - 1) * (z ^ 1 - 1)) := by ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero (mul_ne_zero (mul_ne_zero h21
    h14) h6) h1)
  simpa only [root42Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root42_totient : Nat.totient 42 = 12 := by decide

noncomputable def root52Polynomial : ℚ[X] :=
  X ^ 24 - X ^ 22 + X ^ 20 - X ^ 18 + X ^ 16 - X ^ 14 + X ^ 12 - X ^ 10 + X ^ 8 - X ^ 6 + X ^ 4 -
    X ^ 2 + 1

theorem root52Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 52) :
    aeval z root52Polynomial = 0 := by
  have h26 : z ^ 26 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h4 : z ^ 4 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 52 - 1) * (z ^ 2 - 1) =
      (z ^ 24 - z ^ 22 + z ^ 20 - z ^ 18 + z ^ 16 - z ^ 14 + z ^ 12 - z ^ 10 + z ^ 8 - z ^ 6 + z ^
        4 - z ^ 2 + 1) * ((z ^ 26 - 1) * (z ^ 4 - 1)) := by ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h26 h4)
  simpa only [root52Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root52_totient : Nat.totient 52 = 24 := by decide

noncomputable def root56Polynomial : ℚ[X] :=
  X ^ 24 - X ^ 20 + X ^ 16 - X ^ 12 + X ^ 8 - X ^ 4 + 1

theorem root56Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 56) :
    aeval z root56Polynomial = 0 := by
  have h28 : z ^ 28 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h8 : z ^ 8 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 56 - 1) * (z ^ 4 - 1) =
      (z ^ 24 - z ^ 20 + z ^ 16 - z ^ 12 + z ^ 8 - z ^ 4 + 1) * ((z ^ 28 - 1) * (z ^ 8 - 1)) := by
        ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h28 h8)
  simpa only [root56Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root56_totient : Nat.totient 56 = 24 := by decide

noncomputable def root76Polynomial : ℚ[X] :=
  X ^ 36 - X ^ 34 + X ^ 32 - X ^ 30 + X ^ 28 - X ^ 26 + X ^ 24 - X ^ 22 + X ^ 20 - X ^ 18 + X ^ 16
    - X ^ 14 + X ^ 12 - X ^ 10 + X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1

theorem root76Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 76) :
    aeval z root76Polynomial = 0 := by
  have h38 : z ^ 38 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h4 : z ^ 4 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 76 - 1) * (z ^ 2 - 1) =
      (z ^ 36 - z ^ 34 + z ^ 32 - z ^ 30 + z ^ 28 - z ^ 26 + z ^ 24 - z ^ 22 + z ^ 20 - z ^ 18 + z
        ^ 16 - z ^ 14 + z ^ 12 - z ^ 10 + z ^ 8 - z ^ 6 + z ^ 4 - z ^ 2 + 1) * ((z ^ 38 - 1) * (z
        ^ 4 - 1)) := by ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h38 h4)
  simpa only [root76Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root76_totient : Nat.totient 76 = 36 := by decide

noncomputable def root88Polynomial : ℚ[X] :=
  X ^ 40 - X ^ 36 + X ^ 32 - X ^ 28 + X ^ 24 - X ^ 20 + X ^ 16 - X ^ 12 + X ^ 8 - X ^ 4 + 1

theorem root88Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 88) :
    aeval z root88Polynomial = 0 := by
  have h44 : z ^ 44 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h8 : z ^ 8 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 88 - 1) * (z ^ 4 - 1) =
      (z ^ 40 - z ^ 36 + z ^ 32 - z ^ 28 + z ^ 24 - z ^ 20 + z ^ 16 - z ^ 12 + z ^ 8 - z ^ 4 + 1)
        * ((z ^ 44 - 1) * (z ^ 8 - 1)) := by ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h44 h8)
  simpa only [root88Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root88_totient : Nat.totient 88 = 40 := by decide

noncomputable def root120Polynomial : ℚ[X] :=
  X ^ 32 + X ^ 28 - X ^ 20 - X ^ 16 - X ^ 12 + X ^ 4 + 1

theorem root120Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 120) :
    aeval z root120Polynomial = 0 := by
  have h60 : z ^ 60 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h40 : z ^ 40 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h24 : z ^ 24 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h4 : z ^ 4 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 120 - 1) * (z ^ 20 - 1) * (z ^ 12 - 1) * (z ^ 8 - 1) =
      (z ^ 32 + z ^ 28 - z ^ 20 - z ^ 16 - z ^ 12 + z ^ 4 + 1) * ((z ^ 60 - 1) * (z ^ 40 - 1) * (z
        ^ 24 - 1) * (z ^ 4 - 1)) := by ring
  simp only [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero (mul_ne_zero (mul_ne_zero h60
    h40) h24) h4)
  simpa only [root120Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

theorem root120_totient : Nat.totient 120 = 32 := by decide

end Erdos633b
