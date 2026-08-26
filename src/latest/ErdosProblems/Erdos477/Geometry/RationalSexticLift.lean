/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Rational lifts of proper sextic projections are polynomial.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ProperSexticProjection

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def sexticProjectionEquation (a c : K) (t x w : K[X]) : K[X][X] :=
  X ^ 6 + (C t - C (C a) * X) ^ 6 - C (x ^ 6 + C c * w ^ 6)

lemma natDegree_sexticProjectionEquation (a c : K) (t x w : K[X]) :
    (sexticProjectionEquation a c t x w).natDegree ≤ 6 := by
  have hlin : (C t - C (C a) * X : K[X][X]).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le (by simp) (by simpa using natDegree_pow_le_of_le 6 hlin)
  · simp only [natDegree_C]
    omega

lemma coeff_sexticProjectionEquation_six (a c : K) (t x w : K[X]) :
    (sexticProjectionEquation a c t x w).coeff 6 = C (1 + a ^ 6) := by
  have hlin : (C t - C (C a) * X : K[X][X]).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
  have hpow := coeff_pow_of_natDegree_le (m := 6) hlin
  norm_num only [mul_one, coeff_sub, coeff_C, coeff_C_mul, coeff_X, if_false,
    zero_sub, one_mul, mul_one] at hpow
  simp only [sexticProjectionEquation, coeff_sub, coeff_add, coeff_X_pow, coeff_C]
  norm_num only [if_true, if_false]
  rw [hpow]
  norm_num [neg_pow]

lemma monic_normalized_sexticProjectionEquation (a c : K) (ha : 1 + a ^ 6 ≠ 0)
    (t x w : K[X]) :
    (C (C ((1 + a ^ 6)⁻¹)) * sexticProjectionEquation a c t x w).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 6
  · exact (natDegree_C_mul_le _ _).trans (natDegree_sexticProjectionEquation a c t x w)
  · rw [coeff_C_mul, coeff_sexticProjectionEquation_six, ← map_mul, inv_mul_cancel₀ ha, map_one]

/-- A proper projection has a monic equation for the missing coordinate.
Since `K[T]` is integrally closed, a rational solution has no finite poles. -/
theorem exists_polynomial_sextic_lift (a c : K) (ha : 1 + a ^ 6 ≠ 0)
    (t x w : K[X]) (r : RatFunc K)
    (heq : r ^ 6 + (algebraMap K[X] (RatFunc K) t -
        algebraMap K[X] (RatFunc K) (C a) * r) ^ 6 -
        algebraMap K[X] (RatFunc K) x ^ 6 =
      algebraMap K[X] (RatFunc K) (C c) * algebraMap K[X] (RatFunc K) w ^ 6) :
    ∃ u : K[X], algebraMap K[X] (RatFunc K) u = r ∧
      u ^ 6 + (t - C a * u) ^ 6 - x ^ 6 = C c * w ^ 6 := by
  let F := C (C ((1 + a ^ 6)⁻¹)) * sexticProjectionEquation a c t x w
  have hint : IsIntegral K[X] r := by
    refine ⟨F, monic_normalized_sexticProjectionEquation a c ha t x w, ?_⟩
    change aeval r F = 0
    simp only [F, sexticProjectionEquation, map_mul, map_sub, map_add, map_pow,
      aeval_C, aeval_X]
    have heq' : r ^ 6 + (algebraMap K[X] (RatFunc K) t -
        algebraMap K[X] (RatFunc K) (C a) * r) ^ 6 -
        (algebraMap K[X] (RatFunc K) x ^ 6 +
          algebraMap K[X] (RatFunc K) (C c) * algebraMap K[X] (RatFunc K) w ^ 6) = 0 := by
      linear_combination heq
    rw [heq', mul_zero]
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨u, hu, ?_⟩
  apply (IsFractionRing.injective K[X] (RatFunc K))
  simpa only [map_sub, map_add, map_mul, map_pow, hu] using heq

theorem exists_quadratic_polynomial_sextic_lift (a : ℕ) (c : K) [CharZero K]
    (t x w : K[X]) (ht : t.natDegree ≤ 2) (hx : x.natDegree ≤ 2) (hw : w.natDegree ≤ 2)
    (r : RatFunc K)
    (heq : r ^ 6 + (algebraMap K[X] (RatFunc K) t -
        algebraMap K[X] (RatFunc K) (C (a : K)) * r) ^ 6 -
        algebraMap K[X] (RatFunc K) x ^ 6 =
      algebraMap K[X] (RatFunc K) (C c) * algebraMap K[X] (RatFunc K) w ^ 6) :
    ∃ u : K[X], algebraMap K[X] (RatFunc K) u = r ∧ u.natDegree ≤ 2 ∧
      (t - C (a : K) * u).natDegree ≤ 2 ∧
      u ^ 6 + (t - C (a : K) * u) ^ 6 - x ^ 6 = C c * w ^ 6 := by
  obtain ⟨u, hu, hpoly⟩ := exists_polynomial_sextic_lift (a : K) c
    (proper_nat_slope a) t x w r heq
  have hdegree := quadratic_sextic_lift_degree a c u t x w ht hx hw hpoly
  exact ⟨u, hu, hdegree.1, hdegree.2, hpoly⟩

#print axioms exists_quadratic_polynomial_sextic_lift
-- 'Erdos477.Geometry.exists_quadratic_polynomial_sextic_lift' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
