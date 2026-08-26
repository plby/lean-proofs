/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Irreducibility supplies the nondegeneracy condition in the explicit conic parametrization.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ConicParametrization

namespace Erdos477.Geometry

variable {K : Type*} [Field K]

theorem irreducible_quadratic_no_radial_line (a b c d e s : K)
    (hP : Irreducible (planeQuadratic ![a, b, c, d, e, 0]))
    (hdegree : (planeQuadratic ![a, b, c, d, e, 0]).totalDegree = 2)
    (hlinear : d + e * s = 0) : a + b * s + c * s ^ 2 ≠ 0 := by
  intro hquadratic
  let L : MvPolynomial (Fin 2) K := MvPolynomial.X 1 - MvPolynomial.C s * MvPolynomial.X 0
  let G : MvPolynomial (Fin 2) K := MvPolynomial.C c * MvPolynomial.X 1 +
    MvPolynomial.C (b + c * s) * MvPolynomial.X 0 + MvPolynomial.C e
  have ha : a = -b * s - c * s ^ 2 := by linear_combination hquadratic
  have hd : d = -e * s := by linear_combination hlinear
  have hfactor : planeQuadratic ![a, b, c, d, e, 0] = L * G := by
    rw [planeQuadratic_eq]
    change MvPolynomial.C a * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C b * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C c * MvPolynomial.X 1 ^ 2 + MvPolynomial.C d * MvPolynomial.X 0 +
      MvPolynomial.C e * MvPolynomial.X 1 + MvPolynomial.C 0 = L * G
    rw [ha, hd]
    simp only [MvPolynomial.C_0, map_sub, map_mul, map_pow, map_neg, L, G, map_add]
    ring
  have hLunit : ¬ IsUnit L := by
    intro h
    have hmap := h.map (MvPolynomial.eval (fun _ : Fin 2 => (0 : K)))
    simp [L] at hmap
  have hGunit : IsUnit G := (hP.isUnit_or_isUnit hfactor).resolve_left hLunit
  have hGdegree : G.totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hGunit).2
  have hLdegree : L.totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · simp
    · simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using
        MvPolynomial.totalDegree_mul (MvPolynomial.C s) (MvPolynomial.X (0 : Fin 2))
  have hupper := MvPolynomial.totalDegree_mul L G
  rw [← hfactor, hdegree, hGdegree, add_zero] at hupper
  omega

theorem irreducible_quadratic_parameter_discriminant (a b c d e : K) (he : e ≠ 0)
    (hP : Irreducible (planeQuadratic ![a, b, c, d, e, 0]))
    (hdegree : (planeQuadratic ![a, b, c, d, e, 0]).totalDegree = 2) :
    a * e ^ 2 - b * d * e + c * d ^ 2 ≠ 0 := by
  intro hdisc
  let s := -d / e
  have hlinear : d + e * s = 0 := by dsimp only [s]; field_simp; ring
  have hidentity : e ^ 2 * (a + b * s + c * s ^ 2) =
      a * e ^ 2 - b * d * e + c * d ^ 2 +
        (b * e + c * (e * s - d)) * (d + e * s) := by ring
  rw [hdisc, hlinear, mul_zero, add_zero] at hidentity
  have hquadratic := (mul_eq_zero.mp hidentity).resolve_left (pow_ne_zero _ he)
  exact irreducible_quadratic_no_radial_line a b c d e s hP hdegree hlinear hquadratic

#print axioms irreducible_quadratic_parameter_discriminant
-- 'Erdos477.Geometry.irreducible_quadratic_parameter_discriminant' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
