import ErdosProblems.Erdos633b.CosinePolynomialLifts

/-! An explicit rational polynomial vanishes at every primitive thirtieth
root, by a checked binomial factor identity and primitive nonvanishing. -/

namespace Erdos633b
open Polynomial

noncomputable def root30Polynomial : ℚ[X] := X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

theorem root30Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 30) :
    aeval z root30Polynomial = 0 := by
  have h15 : z ^ 15 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h10 : z ^ 10 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h6 : z ^ 6 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h1 : z - 1 ≠ 0 := by
    simpa only [pow_one] using sub_ne_zero.mpr
      (hz.pow_ne_one_of_pos_of_lt (by decide : 1 ≠ 0) (by decide : 1 < 30))
  have he : (z ^ 30 - 1) * (z ^ 5 - 1) * (z ^ 3 - 1) * (z ^ 2 - 1) =
      (z ^ 8 + z ^ 7 - z ^ 5 - z ^ 4 - z ^ 3 + z + 1) *
        ((z ^ 15 - 1) * (z ^ 10 - 1) * (z ^ 6 - 1) * (z - 1)) := by ring
  rw [hz.pow_eq_one, sub_self, zero_mul, zero_mul, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h15 h10) h6) h1)
  simpa only [root30Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

end Erdos633b
