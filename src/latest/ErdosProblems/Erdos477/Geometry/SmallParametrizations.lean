/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Excluding both linear and quadratic polynomial parametrizations.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticPoints

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- A linear parametrization can be composed with a quadratic parameter
change, preserving the selected point and absence of common coordinate zeroes. -/
theorem no_selected_point_on_small_parametrization (c : ℤ) (hc : c ∉ PowerValues 6)
    (u x y : ℕ) (hu : 1 ≤ u) (hpoint : DiagonalPoint c u x y)
    (f : Fin 4 → K[X]) (hf : ∀ i, (f i).natDegree ≤ 2)
    (hnonconstant : ∃ i, 0 < (f i).natDegree)
    (hroot : ∀ z : K, ∃ i, (f i).eval z ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 - f 2 ^ 6 - C (c : K) * f 3 ^ 6 = 0)
    (t d : K) (hd : d ≠ 0)
    (hval : (f 0).eval t = d * u ∧ (f 1).eval t = d * y ∧
      (f 2).eval t = d * x ∧ (f 3).eval t = d) : False := by
  by_cases htwo : ∃ i, (f i).natDegree = 2
  · exact no_selected_point_on_quadratic_parametrization c hc u x y hu hpoint f hf htwo
      hroot hsum t d hd hval
  have hlinear (i) : (f i).natDegree ≤ 1 := by
    have hbound := hf i
    have hne : (f i).natDegree ≠ 2 := fun h => htwo ⟨i, h⟩
    omega
  obtain ⟨j, hj⟩ := hnonconstant
  have hj1 : (f j).natDegree = 1 := by have h := hlinear j; omega
  let q : K[X] := X ^ 2 + C t
  let g := fun i => (f i).comp q
  have hq : q.natDegree = 2 := natDegree_X_pow_add_C
  have hg (i) : (g i).natDegree ≤ 2 := by
    rw [show (g i).natDegree = (f i).natDegree * q.natDegree from natDegree_comp, hq]
    have h := hlinear i
    omega
  have hgj : (g j).natDegree = 2 := by
    rw [show (g j).natDegree = (f j).natDegree * q.natDegree from natDegree_comp, hj1, hq]
  have hgroot (z : K) : ∃ i, (g i).eval z ≠ 0 := by
    obtain ⟨i, hi⟩ := hroot (q.eval z)
    exact ⟨i, by simpa only [g, eval_comp] using hi⟩
  have hgsum : g 0 ^ 6 + g 1 ^ 6 - g 2 ^ 6 - C (c : K) * g 3 ^ 6 = 0 := by
    have h := congrArg (compRingHom q) hsum
    simpa only [map_sub, map_add, map_mul, map_pow, map_zero,
      coe_compRingHom_apply, C_comp, g] using h
  have hgval : (g 0).eval 0 = d * u ∧ (g 1).eval 0 = d * y ∧
      (g 2).eval 0 = d * x ∧ (g 3).eval 0 = d := by
    simpa [g, q] using hval
  exact no_selected_point_on_quadratic_parametrization c hc u x y hu hpoint g hg ⟨j, hgj⟩
    hgroot hgsum 0 d hd hgval

#print axioms no_selected_point_on_small_parametrization
-- 'Erdos477.Geometry.no_selected_point_on_small_parametrization' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
