/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Low-degree irreducible divisors of a sixth-power binomial.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticSixthZero

namespace Erdos477.Geometry

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

lemma natDegree_monic_quadratic (b c : R) : (X ^ 2 + C b * X + C c : R[X]).natDegree = 2 := by
  rw [natDegree_add_C, natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · have h := natDegree_C_mul_le b (X : R[X])
    simp only [natDegree_X] at h
    simpa only [natDegree_X_pow] using h.trans_lt (by decide : 1 < 2)

theorem quadratic_dvd_sixth_sub_constant (b c H : R)
    (hdiv : X ^ 2 + C b * X + C c ∣ X ^ 6 - C H) :
    quadraticSixthLinear b c = 0 ∧ quadraticSixthConstant b c = H := by
  let A := quadraticSixthLinear b c
  let D := quadraticSixthConstant b c
  have hrem := quadratic_dvd_sixth_sub_remainder b c
  have hsub := dvd_sub hdiv hrem
  have hidentity : (X ^ 6 - C H : R[X]) - (X ^ 6 - (C A * X + C D)) =
      C A * X + C (D - H) := by rw [map_sub]; ring
  change X ^ 2 + C b * X + C c ∣ (X ^ 6 - C H) - (X ^ 6 - (C A * X + C D)) at hsub
  rw [hidentity] at hsub
  have hdegree : (C A * X + C (D - H) : R[X]).natDegree ≤ 1 := by
    rw [natDegree_add_C]
    simpa only [natDegree_X] using natDegree_C_mul_le A (X : R[X])
  have hzero : (C A * X + C (D - H) : R[X]) = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hsub (by rw [natDegree_monic_quadratic]; omega)
  have hA := congrArg (fun p : R[X] => p.coeff 1) hzero
  have hD := congrArg (fun p : R[X] => p.coeff 0) hzero
  norm_num [coeff_add, coeff_C_mul_X] at hA hD
  exact ⟨hA, sub_eq_zero.mp hD⟩

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem irreducible_quadratic_sixth_divisor (b c H : K[X])
    (hP : Irreducible (X ^ 2 + C b * X + C c : K[X][X]))
    (hdiv : X ^ 2 + C b * X + C c ∣ X ^ 6 - C H) :
    b = 0 ∧ H = (-c) ^ 3 := by
  obtain ⟨hA, hH⟩ := quadratic_dvd_sixth_sub_constant b c H hdiv
  have hb := quadraticSixthLinear_zero_forces_zero_trace b c hP hA
  refine ⟨hb, ?_⟩
  rw [hb, quadraticSixthConstant_zero] at hH
  calc
    H = -c ^ 3 := hH.symm
    _ = (-c) ^ 3 := by ring

#print axioms irreducible_quadratic_sixth_divisor
-- 'Erdos477.Geometry.irreducible_quadratic_sixth_divisor' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
