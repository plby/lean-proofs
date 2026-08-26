/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Low-degree plane parametrizations with a prescribed regular affine point.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ConicAtPoint
import ErdosProblems.Erdos477.Geometry.RationalEvaluation

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

structure SmallPlaneParametrization (P : MvPolynomial (Fin 2) K) (z : Fin 2 → K) where
  coordinate : Fin 3 → K[X]
  parameter : K
  scale : K
  degree_le : ∀ i, (coordinate i).natDegree ≤ 2
  nonconstant : ∃ i, 0 < (coordinate i).natDegree
  no_common_root : ∀ r : K, ∃ i, (coordinate i).eval r ≠ 0
  denominator_ne_zero : coordinate 2 ≠ 0
  scale_ne_zero : scale ≠ 0
  eval_first : (coordinate 0).eval parameter = scale * z 0
  eval_second : (coordinate 1).eval parameter = scale * z 1
  eval_denominator : (coordinate 2).eval parameter = scale
  equation : MvPolynomial.eval₂Hom RatFunc.C (rationalPlaneCoordinates coordinate) P = 0

theorem exists_small_conic_parametrization_second_chart (P : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hdegree : P.totalDegree = 2)
    (z : Fin 2 → K) (hroot : MvPolynomial.eval z P = 0)
    (hgradient : MvPolynomial.eval z (MvPolynomial.pderiv 1 P) ≠ 0) :
    Nonempty (SmallPlaneParametrization P z) := by
  obtain ⟨f, s, v, hf, htwo, hroot, hden, hv, h0, h1, h2, heq⟩ :=
    exists_conic_parametrization_at_point P hP hdegree z hroot hgradient
  refine ⟨{
    coordinate := f
    parameter := s
    scale := v
    degree_le := hf
    nonconstant := ?_
    no_common_root := ?_
    denominator_ne_zero := hden
    scale_ne_zero := hv
    eval_first := h0
    eval_second := h1
    eval_denominator := h2
    equation := heq }⟩
  · obtain ⟨i, hi⟩ := htwo
    exact ⟨i, by rw [hi]; decide⟩
  · intro r
    by_contra! h
    exact hroot r h

theorem SmallPlaneParametrization.evaluatesAt {P : MvPolynomial (Fin 2) K} {z : Fin 2 → K}
    (h : SmallPlaneParametrization P z) (i : Fin 2) :
    EvaluatesAt h.parameter (rationalPlaneCoordinates h.coordinate i) (z i) := by
  have hden : EvaluatesAt h.parameter
      (algebraMap K[X] (RatFunc K) (h.coordinate 2)) h.scale := by
    simpa only [h.eval_denominator] using evaluatesAt_polynomial h.parameter (h.coordinate 2)
  fin_cases i
  · have hnum : EvaluatesAt h.parameter
        (algebraMap K[X] (RatFunc K) (h.coordinate 0)) (h.scale * z 0) := by
      simpa only [h.eval_first] using evaluatesAt_polynomial h.parameter (h.coordinate 0)
    have hv := hnum.div hden h.scale_ne_zero
    change EvaluatesAt h.parameter
      (algebraMap K[X] (RatFunc K) (h.coordinate 0) /
        algebraMap K[X] (RatFunc K) (h.coordinate 2)) (z 0)
    simpa only [mul_div_cancel_left₀ _ h.scale_ne_zero] using hv
  · have hnum : EvaluatesAt h.parameter
        (algebraMap K[X] (RatFunc K) (h.coordinate 1)) (h.scale * z 1) := by
      simpa only [h.eval_second] using evaluatesAt_polynomial h.parameter (h.coordinate 1)
    have hv := hnum.div hden h.scale_ne_zero
    change EvaluatesAt h.parameter
      (algebraMap K[X] (RatFunc K) (h.coordinate 1) /
        algebraMap K[X] (RatFunc K) (h.coordinate 2)) (z 1)
    simpa only [mul_div_cancel_left₀ _ h.scale_ne_zero] using hv

#print axioms SmallPlaneParametrization.evaluatesAt
-- 'Erdos477.Geometry.SmallPlaneParametrization.evaluatesAt' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
