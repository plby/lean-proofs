/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Polynomial certificates excluding smooth selected points on low-degree projected curves.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SmallRationalLifts
import ErdosProblems.Erdos477.Geometry.LineAtPoint

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def sexticRationalCertificate (a c : K)
    (N D : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  N ^ 6 + (MvPolynomial.X 0 * D - MvPolynomial.C a * N) ^ 6 -
    MvPolynomial.X 1 ^ 6 * D ^ 6 - MvPolynomial.C c * D ^ 6

variable [IsAlgClosed K] [CharZero K]

theorem no_smooth_selected_point_of_rational_certificate
    (c : ℤ) (hc : c ∉ PowerValues 6) (u x y : ℕ) (hu : 1 ≤ u)
    (hpoint : DiagonalPoint c u x y) (a : ℕ)
    (P N D : MvPolynomial (Fin 2) K) (hP : Irreducible P) (hdegree : P.totalDegree ≤ 2)
    (hdiv : P ∣ sexticRationalCertificate (a : K) (c : K) N D)
    (hroot : MvPolynomial.eval ![(y : K) + (a : K) * u, (x : K)] P = 0)
    (hgradient : ∃ i, MvPolynomial.eval ![(y : K) + (a : K) * u, (x : K)]
      (MvPolynomial.pderiv i P) ≠ 0)
    (hden : MvPolynomial.eval ![(y : K) + (a : K) * u, (x : K)] D ≠ 0)
    (hinverse : MvPolynomial.eval ![(y : K) + (a : K) * u, (x : K)] N =
      (u : K) * MvPolynomial.eval ![(y : K) + (a : K) * u, (x : K)] D) : False := by
  let z : Fin 2 → K := ![(y : K) + (a : K) * u, (x : K)]
  have hparam : Nonempty (SmallPlaneParametrization P z) := by
    by_cases hsmall : P.totalDegree ≤ 1
    · exact exists_small_line_parametrization P hsmall z hroot hgradient
    · exact exists_small_conic_parametrization P hP (by omega) z hroot hgradient
  obtain ⟨p⟩ := hparam
  let φ := MvPolynomial.eval₂Hom RatFunc.C (rationalPlaneCoordinates p.coordinate)
  let n := φ N
  let d := φ D
  have hnval : EvaluatesAt p.parameter n (MvPolynomial.eval z N) :=
    evaluatesAt_mvPolynomial p.parameter _ z p.evaluatesAt N
  have hdval : EvaluatesAt p.parameter d (MvPolynomial.eval z D) :=
    evaluatesAt_mvPolynomial p.parameter _ z p.evaluatesAt D
  have hd : d ≠ 0 := hdval.ne_zero hden
  have hr : EvaluatesAt p.parameter (n / d) (u : K) := by
    have h := hnval.div hdval hden
    rw [hinverse, mul_div_cancel_right₀ _ hden] at h
    exact h
  have hcert : φ (sexticRationalCertificate (a : K) (c : K) N D) = 0 := by
    obtain ⟨G, hG⟩ := hdiv
    rw [hG, map_mul, show φ P = 0 from p.equation, zero_mul]
  simp only [sexticRationalCertificate, map_sub, map_add, map_pow, map_mul,
    φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C] at hcert
  change n ^ 6 + (rationalPlaneCoordinates p.coordinate 0 * d - RatFunc.C (a : K) * n) ^ 6 -
    (rationalPlaneCoordinates p.coordinate 1) ^ 6 * d ^ 6 - RatFunc.C (c : K) * d ^ 6 = 0 at hcert
  have hsextic : (n / d) ^ 6 +
      (rationalPlaneCoordinates p.coordinate 0 - RatFunc.C (a : K) * (n / d)) ^ 6 -
      (rationalPlaneCoordinates p.coordinate 1) ^ 6 = RatFunc.C (c : K) := by
    field_simp
    linear_combination hcert
  exact no_selected_point_on_small_rational_lift c hc u x y hu hpoint a p.coordinate p.degree_le
    p.nonconstant p.no_common_root p.parameter p.scale p.scale_ne_zero
    ⟨p.eval_first, p.eval_second, p.eval_denominator⟩ (n / d) hr hsextic

#print axioms no_smooth_selected_point_of_rational_certificate
-- 'Erdos477.Geometry.no_smooth_selected_point_of_rational_certificate' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
