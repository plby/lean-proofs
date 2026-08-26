/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Linear homogeneous coordinates through a prescribed point of an affine line.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ConicCharts

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def planeLinear (a b c : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 + MvPolynomial.C c

theorem exists_planeLinear_of_totalDegree_le (P : MvPolynomial (Fin 2) K)
    (hP : P.totalDegree ≤ 1) : ∃ a b c : K, P = planeLinear a b c := by
  have hhigh (m : Fin 2 →₀ ℕ) (hm : m 0 + m 1 = 2) : P.coeff m = 0 := by
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    change P.totalDegree < m.sum (fun _ n => n)
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two, hm]
    omega
  have h0 := hhigh (quadraticExponent 0) (by norm_num [quadraticExponent])
  have h1 := hhigh (quadraticExponent 1) (by norm_num [quadraticExponent])
  have h2 := hhigh (quadraticExponent 2) (by
    change planeExponent 0 2 0 + planeExponent 0 2 1 = 2
    simp)
  let a := P.coeff (quadraticExponent 3)
  let b := P.coeff (quadraticExponent 4)
  let c := P.coeff (quadraticExponent 5)
  have hvec : (fun i => P.coeff (quadraticExponent i)) = ![0, 0, 0, a, b, c] := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · rfl
    · rfl
    · rfl
  refine ⟨a, b, c, ?_⟩
  rw [eq_planeQuadratic_of_totalDegree_le P (hP.trans (by decide)), hvec, planeQuadratic_eq]
  simp [planeLinear]

theorem exists_small_line_parametrization_second_chart (P : MvPolynomial (Fin 2) K)
    (hdegree : P.totalDegree ≤ 1) (z : Fin 2 → K) (hroot : MvPolynomial.eval z P = 0)
    (hgradient : MvPolynomial.eval z (MvPolynomial.pderiv 1 P) ≠ 0) :
    Nonempty (SmallPlaneParametrization P z) := by
  obtain ⟨a, b, c, hP⟩ := exists_planeLinear_of_totalDegree_le P hdegree
  have hb : b ≠ 0 := by simpa [hP, planeLinear] using hgradient
  have hpoint : a * z 0 + b * z 1 + c = 0 := by simpa [hP, planeLinear] using hroot
  let f : Fin 3 → K[X] := ![C b * X + C (z 0), C (-a) * X + C (z 1), 1]
  refine ⟨{
    coordinate := f
    parameter := 0
    scale := 1
    degree_le := ?_
    nonconstant := ?_
    no_common_root := ?_
    denominator_ne_zero := one_ne_zero
    scale_ne_zero := one_ne_zero
    eval_first := ?_
    eval_second := ?_
    eval_denominator := by simp [f]
    equation := ?_ }⟩
  · intro i
    fin_cases i
    · exact natDegree_linear_le.trans (by decide)
    · exact natDegree_linear_le.trans (by decide)
    · simp [f]
  · refine ⟨0, ?_⟩
    change 0 < (C b * X + C (z 0) : K[X]).natDegree
    rw [natDegree_linear hb]
    decide
  · intro r
    exact ⟨2, by simp [f]⟩
  · simp [f]
  · simp [f]
  · rw [hP]
    simp [planeLinear, rationalPlaneCoordinates, f]
    have h := congrArg RatFunc.C hpoint
    simp only [map_add, map_mul, map_zero] at h
    linear_combination h

theorem exists_small_line_parametrization (P : MvPolynomial (Fin 2) K)
    (hdegree : P.totalDegree ≤ 1) (z : Fin 2 → K) (hroot : MvPolynomial.eval z P = 0)
    (hgradient : ∃ i, MvPolynomial.eval z (MvPolynomial.pderiv i P) ≠ 0) :
    Nonempty (SmallPlaneParametrization P z) := by
  obtain ⟨i, hi⟩ := hgradient
  fin_cases i
  · have hQdegree : (MvPolynomial.rename planeSwap P).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_renameEquiv planeSwap P).le.trans hdegree
    have hQroot : MvPolynomial.eval (swappedPoint z) (MvPolynomial.rename planeSwap P) = 0 := by
      rw [MvPolynomial.eval_rename, swappedPoint_comp_swap]
      exact hroot
    have hderiv : MvPolynomial.pderiv 1 (MvPolynomial.rename planeSwap P) =
        MvPolynomial.rename planeSwap (MvPolynomial.pderiv 0 P) := by
      simpa only [planeSwap, Equiv.swap_apply_left] using
        MvPolynomial.pderiv_rename planeSwap.injective 0 P
    have hQgradient : MvPolynomial.eval (swappedPoint z)
        (MvPolynomial.pderiv 1 (MvPolynomial.rename planeSwap P)) ≠ 0 := by
      rw [hderiv, MvPolynomial.eval_rename, swappedPoint_comp_swap]
      exact hi
    obtain ⟨h⟩ := exists_small_line_parametrization_second_chart _ hQdegree _ hQroot hQgradient
    exact ⟨h.swap⟩
  · exact exists_small_line_parametrization_second_chart P hdegree z hroot hi

#print axioms exists_small_line_parametrization
-- 'Erdos477.Geometry.exists_small_line_parametrization' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
