/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Quadratic homogeneous coordinates on a conic through a prescribed smooth affine point.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ProjectivePlaneTranslation

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

/-- The parametrization is defined over the coefficient field, has no common
finite coordinate zero, and reaches the specified point at a finite parameter. -/
theorem exists_conic_parametrization_at_point (P : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hdegree : P.totalDegree = 2)
    (z : Fin 2 → K) (hroot : MvPolynomial.eval z P = 0)
    (hgradient : MvPolynomial.eval z (MvPolynomial.pderiv 1 P) ≠ 0) :
    ∃ f : Fin 3 → K[X], ∃ s v : K,
      (∀ i, (f i).natDegree ≤ 2) ∧ (∃ i, (f i).natDegree = 2) ∧
      (∀ r : K, ¬ ∀ i, (f i).eval r = 0) ∧ f 2 ≠ 0 ∧ v ≠ 0 ∧
      (f 0).eval s = v * z 0 ∧ (f 1).eval s = v * z 1 ∧ (f 2).eval s = v ∧
      MvPolynomial.eval₂Hom RatFunc.C (rationalPlaneCoordinates f) P = 0 := by
  obtain ⟨a, b, c, d, e, he, hdisc, hcenter⟩ :=
    exists_centered_conic_coefficients P hP hdegree z hroot hgradient
  let f := conicCoordinates a b c d e
  let g := homogeneousPlaneTranslate z f
  have hfdegree : ∀ i, (f i).natDegree ≤ 2 := degree_conicCoordinates a b c d e
  have hf2 : f 2 ≠ 0 := conicDenominator_ne_zero a b c d e he hdisc
  have hfroot : ∀ r : K, ¬ ∀ i, (f i).eval r = 0 :=
    conicCoordinates_no_common_root a b c d e hdisc
  obtain ⟨v, hv, h0, h1, h2⟩ := conicCoordinates_at_base a b c d e he hdisc
  have hgdegree : ∀ i, (g i).natDegree ≤ 2 := degree_homogeneousPlaneTranslate z f 2 hfdegree
  have hgtwo : ∃ i, (g i).natDegree = 2 := homogeneousPlaneTranslate_has_degree_two z f hfdegree
    ⟨1, conicCoordinates_degree_two a b c d e he⟩
  have hgroot : ∀ r : K, ¬ ∀ i, (g i).eval r = 0 :=
    homogeneousPlaneTranslate_no_common_root z f hfroot
  refine ⟨g, -d / e, v, hgdegree, hgtwo, hgroot, hf2, hv, ?_, ?_, h2, ?_⟩
  · change (f 0 + C (z 0) * f 2).eval (-d / e) = v * z 0
    change (f 0).eval (-d / e) = 0 at h0
    change (f 2).eval (-d / e) = v at h2
    rw [eval_add, eval_mul, eval_C, h0, h2, zero_add, mul_comm]
  · change (f 1 + C (z 1) * f 2).eval (-d / e) = v * z 1
    change (f 1).eval (-d / e) = 0 at h1
    change (f 2).eval (-d / e) = v at h2
    rw [eval_add, eval_mul, eval_C, h1, h2, zero_add, mul_comm]
  · change MvPolynomial.eval₂Hom RatFunc.C
      (rationalPlaneCoordinates (homogeneousPlaneTranslate z f)) P = 0
    rw [eval₂_homogeneousPlaneTranslate z f hf2, hcenter]
    exact conicRationalCoordinates_root a b c d e he hdisc

#print axioms exists_conic_parametrization_at_point
-- 'Erdos477.Geometry.exists_conic_parametrization_at_point' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
