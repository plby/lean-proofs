/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Normalizing an irreducible conic at a point with nonzero second partial derivative.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ConicIrreducible
import ErdosProblems.Erdos477.Geometry.PlaneTranslation

namespace Erdos477.Geometry

variable {K : Type*} [Field K]

theorem exists_centered_conic_coefficients (P : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hdegree : P.totalDegree = 2)
    (z : Fin 2 → K) (hroot : MvPolynomial.eval z P = 0)
    (hgradient : MvPolynomial.eval z (MvPolynomial.pderiv 1 P) ≠ 0) :
    ∃ a b c d e : K, e ≠ 0 ∧ a * e ^ 2 - b * d * e + c * d ^ 2 ≠ 0 ∧
      planeTranslate z P = planeQuadratic ![a, b, c, d, e, 0] := by
  let Q := planeTranslate z P
  let v : Fin 6 → K := fun i => Q.coeff (quadraticExponent i)
  have hQdegree : Q.totalDegree = 2 := (totalDegree_planeTranslate z P).trans hdegree
  have hQ : Q = planeQuadratic v := eq_planeQuadratic_of_totalDegree_le Q hQdegree.le
  have hconstant : v 5 = 0 := by
    have h := coeff_zero_planeTranslate z P
    rw [hroot] at h
    simpa [v, quadraticExponent, planeExponent, Q] using h
  have hlinear : v 4 ≠ 0 := by
    have h := coeff_linear_planeTranslate z P 1
    have heq : v 4 = MvPolynomial.eval z (MvPolynomial.pderiv 1 P) := by
      simpa [v, quadraticExponent, planeExponent, Q] using h
    rwa [heq]
  have hvec : v = ![v 0, v 1, v 2, v 3, v 4, 0] := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hconstant
  have hQ' : Q = planeQuadratic ![v 0, v 1, v 2, v 3, v 4, 0] := by
    conv_lhs => rw [hQ]
    exact congrArg planeQuadratic hvec
  have hirr : Irreducible (planeQuadratic ![v 0, v 1, v 2, v 3, v 4, 0]) := by
    rw [← hQ']
    exact irreducible_planeTranslate z P hP
  have hdeg : (planeQuadratic ![v 0, v 1, v 2, v 3, v 4, 0]).totalDegree = 2 := by
    rw [← hQ']
    exact hQdegree
  exact ⟨v 0, v 1, v 2, v 3, v 4, hlinear,
    irreducible_quadratic_parameter_discriminant _ _ _ _ _ hlinear hirr hdeg, hQ'⟩

#print axioms exists_centered_conic_coefficients
-- 'Erdos477.Geometry.exists_centered_conic_coefficients' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
