/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Excluding regular rational lifts of low-degree projected parametrizations.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SmallParametrizations
import ErdosProblems.Erdos477.Geometry.RationalSexticLift
import ErdosProblems.Erdos477.Geometry.ProjectivePlaneTranslation
import ErdosProblems.Erdos477.Geometry.RationalEvaluation

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

lemma homogenize_sextic_identity (u t x w a c : K) (hw : w ≠ 0)
    (h : u ^ 6 + (t / w - a * u) ^ 6 - (x / w) ^ 6 = c) :
    (w * u) ^ 6 + (t - a * (w * u)) ^ 6 - x ^ 6 = c * w ^ 6 := by
  field_simp at h
  linear_combination h

variable [IsAlgClosed K] [CharZero K]

/-- A rational inverse regular at the selected point cannot lift a
nonconstant projected parametrization of degree at most two to the sextic. -/
theorem no_selected_point_on_small_rational_lift (c : ℤ) (hc : c ∉ PowerValues 6)
    (u x y : ℕ) (hu : 1 ≤ u) (hpoint : DiagonalPoint c u x y) (a : ℕ)
    (f : Fin 3 → K[X]) (hf : ∀ i, (f i).natDegree ≤ 2)
    (hnonconstant : ∃ i, 0 < (f i).natDegree)
    (hroot : ∀ z : K, ∃ i, (f i).eval z ≠ 0)
    (s v : K) (hv : v ≠ 0)
    (hval : (f 0).eval s = v * ((y : K) + (a : K) * (u : K)) ∧
      (f 1).eval s = v * x ∧ (f 2).eval s = v)
    (r : RatFunc K) (hr : EvaluatesAt s r (u : K))
    (heq : r ^ 6 + (rationalPlaneCoordinates f 0 - RatFunc.C (a : K) * r) ^ 6 -
      (rationalPlaneCoordinates f 1) ^ 6 = RatFunc.C (c : K)) : False := by
  have hW : f 2 ≠ 0 := by
    intro hzero
    have h := hval.2.2
    rw [hzero, eval_zero] at h
    exact hv h.symm
  have hWmap : algebraMap K[X] (RatFunc K) (f 2) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hW
  have hhom := homogenize_sextic_identity r
    (algebraMap K[X] (RatFunc K) (f 0)) (algebraMap K[X] (RatFunc K) (f 1))
    (algebraMap K[X] (RatFunc K) (f 2)) (RatFunc.C (a : K)) (RatFunc.C (c : K)) hWmap heq
  obtain ⟨U, hU, hpoly⟩ := exists_polynomial_sextic_lift (a : K) (c : K) (proper_nat_slope a)
    (f 0) (f 1) (f 2) (algebraMap K[X] (RatFunc K) (f 2) * r)
    (by simpa only [RatFunc.algebraMap_C] using hhom)
  have hdegrees := quadratic_sextic_lift_degree a (c : K) U (f 0) (f 1) (f 2)
    (hf 0) (hf 1) (hf 2) hpoly
  let g : Fin 4 → K[X] := ![U, f 0 - C (a : K) * U, f 1, f 2]
  have hg (i) : (g i).natDegree ≤ 2 := by
    fin_cases i
    · exact hdegrees.1
    · exact hdegrees.2
    · exact hf 1
    · exact hf 2
  have hgnonconstant : ∃ i, 0 < (g i).natDegree := by
    by_contra! h
    have hzero (i) : (g i).natDegree = 0 := Nat.eq_zero_of_le_zero (h i)
    have hUdegree : U.natDegree ≤ 0 := (hzero 0).le
    have hYdegree : (f 0 - C (a : K) * U).natDegree ≤ 0 := (hzero 1).le
    have hTdegree : (f 0).natDegree ≤ 0 := by
      have hid : f 0 = (f 0 - C (a : K) * U) + C (a : K) * U := by ring
      conv_lhs => rw [hid]
      exact (natDegree_add_le _ _).trans
        (max_le hYdegree ((natDegree_C_mul_le _ _).trans hUdegree))
    obtain ⟨i, hi⟩ := hnonconstant
    fin_cases i
    · exact (Nat.not_lt_of_ge hTdegree) hi
    · have h := hzero 2
      change (f 1).natDegree = 0 at h
      change 0 < (f 1).natDegree at hi
      omega
    · have h := hzero 3
      change (f 2).natDegree = 0 at h
      change 0 < (f 2).natDegree at hi
      omega
  have hgroot (z : K) : ∃ i, (g i).eval z ≠ 0 := by
    by_contra! h
    have h0 : U.eval z = 0 := h 0
    have h1 : (f 0 - C (a : K) * U).eval z = 0 := h 1
    have hT : (f 0).eval z = 0 := by
      simpa only [eval_sub, eval_mul, h0, mul_zero, sub_zero] using h1
    obtain ⟨i, hi⟩ := hroot z
    fin_cases i
    · exact hi hT
    · exact hi (h 2)
    · exact hi (h 3)
  have hgsum : g 0 ^ 6 + g 1 ^ 6 - g 2 ^ 6 - C (c : K) * g 3 ^ 6 = 0 :=
    sub_eq_zero.mpr hpoly
  have hWvalue : EvaluatesAt s (algebraMap K[X] (RatFunc K) (f 2)) v := by
    simpa only [hval.2.2] using evaluatesAt_polynomial s (f 2)
  have hUvalue : U.eval s = v * (u : K) := by
    have h := hWvalue.mul hr
    rw [← hU] at h
    exact (evaluatesAt_polynomial s U).unique h
  have hYvalue : (f 0 - C (a : K) * U).eval s = v * (y : K) := by
    rw [eval_sub, eval_mul, eval_C, hval.1, hUvalue]
    ring
  exact no_selected_point_on_small_parametrization c hc u x y hu hpoint g hg hgnonconstant
    hgroot hgsum s v hv ⟨hUvalue, hYvalue, hval.2.1, hval.2.2⟩

#print axioms no_selected_point_on_small_rational_lift
-- 'Erdos477.Geometry.no_selected_point_on_small_rational_lift' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
