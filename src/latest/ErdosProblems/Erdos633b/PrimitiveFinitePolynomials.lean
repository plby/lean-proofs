import ErdosProblems.Erdos633b.Primitive30Polynomial

/-! Explicit annihilators for primitive orders24 and60, justified by
binomial identities and the exact order of a square. -/

namespace Erdos633b
open Polynomial

noncomputable def root24Polynomial : ℚ[X] := X ^ 8 - X ^ 4 + 1

theorem root24Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 24) :
    aeval z root24Polynomial = 0 := by
  have h12 : z ^ 12 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h8 : z ^ 8 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 24 - 1) * (z ^ 4 - 1) =
      (z ^ 8 - z ^ 4 + 1) * ((z ^ 12 - 1) * (z ^ 8 - 1)) := by ring
  rw [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h12 h8)
  simpa only [root24Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

noncomputable def root60Polynomial : ℚ[X] :=
  X ^ 16 + X ^ 14 - X ^ 10 - X ^ 8 - X ^ 6 + X ^ 2 + 1

theorem root60Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 60) :
    aeval z root60Polynomial = 0 := by
  have hz2 : IsPrimitiveRoot (z ^ 2) 30 := by
    simpa only [Nat.reduceDiv] using hz.pow_of_dvd (by decide : 2 ≠ 0) (by decide : 2 ∣ 60)
  have hh := root30Polynomial_vanishes (z ^ 2) hz2
  simp only [root30Polynomial, map_add, map_sub, map_pow, aeval_X, map_one,
    ← pow_mul, Nat.reduceMul] at hh
  simpa only [root60Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

end Erdos633b
