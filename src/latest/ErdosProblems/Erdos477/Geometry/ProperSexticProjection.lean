/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Polynomial degree control for proper projections of the affine sextic.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

theorem natDegree_sextic_lift_le (a c : K) (ha : 1 + a ^ 6 ≠ 0)
    (u t x w : K[X]) (D : ℕ)
    (ht : t.natDegree ≤ D) (hx : x.natDegree ≤ D) (hw : w.natDegree ≤ D)
    (heq : u ^ 6 + (t - C a * u) ^ 6 - x ^ 6 = C c * w ^ 6) :
    u.natDegree ≤ D := by
  by_contra h
  have hn : D < u.natDegree := Nat.lt_of_not_ge h
  have hu : u ≠ 0 := by intro hzero; rw [hzero, natDegree_zero] at hn; omega
  have htn := ht.trans_lt hn
  have hxn := hx.trans_lt hn
  have hwn := hw.trans_lt hn
  have hyv : (t - C a * u).natDegree ≤ u.natDegree :=
    (natDegree_sub_le _ _).trans (max_le htn.le (natDegree_C_mul_le _ _))
  have htop := congrArg (fun p : K[X] => p.coeff (6 * u.natDegree)) heq
  rw [coeff_sub, coeff_add, coeff_C_mul,
    coeff_pow_of_natDegree_le (le_refl u.natDegree),
    coeff_pow_of_natDegree_le hyv,
    coeff_pow_of_natDegree_le hxn.le,
    coeff_pow_of_natDegree_le hwn.le,
    coeff_eq_zero_of_natDegree_lt hxn, coeff_eq_zero_of_natDegree_lt hwn,
    coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt htn] at htop
  have hmul : u.leadingCoeff ^ 6 * (1 + a ^ 6) = 0 := by
    calc
      _ = u.coeff u.natDegree ^ 6 + (0 - a * u.coeff u.natDegree) ^ 6 -
          0 ^ 6 - c * 0 ^ 6 := by rw [coeff_natDegree]; ring
      _ = 0 := sub_eq_zero.mpr htop
  exact (mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hu)) ha) hmul

lemma proper_nat_slope [CharZero K] (a : ℕ) : 1 + (a : K) ^ 6 ≠ 0 := by
  have h : (1 : ℕ) + a ^ 6 ≠ 0 := by omega
  exact_mod_cast h

/-- Once a rational lift has been shown polynomial, its degree cannot
exceed that of the projected homogeneous coordinates. -/
theorem quadratic_sextic_lift_degree (a : ℕ) (c : K)
    [CharZero K] (u t x w : K[X])
    (ht : t.natDegree ≤ 2) (hx : x.natDegree ≤ 2) (hw : w.natDegree ≤ 2)
    (heq : u ^ 6 + (t - C (a : K) * u) ^ 6 - x ^ 6 = C c * w ^ 6) :
    u.natDegree ≤ 2 ∧ (t - C (a : K) * u).natDegree ≤ 2 := by
  have hu := natDegree_sextic_lift_le (a : K) c (proper_nat_slope a) u t x w 2 ht hx hw heq
  exact ⟨hu, (natDegree_sub_le _ _).trans (max_le ht ((natDegree_C_mul_le _ _).trans hu))⟩

#print axioms quadratic_sextic_lift_degree
-- 'Erdos477.Geometry.quadratic_sextic_lift_degree' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
