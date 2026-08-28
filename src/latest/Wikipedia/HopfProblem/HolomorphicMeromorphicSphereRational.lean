import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRationalPolynomial
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereEvaluationArithmetic
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereScalar

/-!
# The genuine meromorphic function field of the sphere is rational

The field on the sphere is the full original sheaf of local fractions,
not a field defined by a rational-function presentation. Every native
section has scalar meromorphic representatives in both actual charts.
Scalar rationality and the native identity principle then show that it
is a quotient of polynomials in the genuine affine coordinate.

This gives an actual complex-algebra equivalence with Mathlib's rational
function field, preserving the original coordinate and constants.
-/

noncomputable section

open Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative

/-- Rational functions act through the actual meromorphic coordinate.
Injectivity of polynomial evaluation permits the fraction-field lift. -/
def rationalMap : RatFunc ℂ →ₐ[ℂ] Function 𝓘(ℂ) RiemannSphere :=
  RatFunc.liftAlgHom polynomialMap
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      polynomialMap.toRingHom polynomialMap_injective)

theorem rationalMap_apply_div (P Q : Polynomial ℂ) :
    rationalMap (algebraMap (Polynomial ℂ) (RatFunc ℂ) P /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) = polynomialMap P / polynomialMap Q :=
  RatFunc.liftAlgHom_apply_div polynomialMap _ P Q

@[simp] theorem rationalMap_polynomial (P : Polynomial ℂ) :
    rationalMap (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) = polynomialMap P := by
  simpa only [map_one, div_one] using rationalMap_apply_div P 1

@[simp] theorem rationalMap_X : rationalMap RatFunc.X = coordinate :=
  (rationalMap_polynomial Polynomial.X).trans polynomialMap_X

theorem rationalMap_injective : _root_.Function.Injective rationalMap :=
  rationalMap.injective

/-- Every original native meromorphic function is an actual quotient
of polynomial sections, with a nonzero polynomial denominator. -/
theorem exists_polynomial_fraction (s : Function 𝓘(ℂ) RiemannSphere) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ s = polynomialMap P / polynomialMap Q := by
  obtain ⟨P, Q, hQ, hfinite⟩ := SphereScalar.exists_polynomial_quotient
    (SphereRepresentative.finiteValue_meromorphicOn s)
    (SphereRepresentative.finiteValue_comp_inv_meromorphicAt_zero s)
  refine ⟨P, Q, hQ, ?_⟩
  apply SphereRepresentative.eq_of_finiteValue_eventuallyEq s
    (polynomialMap P / polynomialMap Q) 0
  have hquot : SphereRepresentative.finiteValue (polynomialMap P / polynomialMap Q) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun w => P.eval w / Q.eval w) := by
    simpa only [polynomialMap_finiteValue] using
      SphereEvaluation.finiteValue_div_eventuallyEq (polynomialMap P) (polynomialMap Q) 0
  exact (hfinite 0).trans hquot.symm

/-- Surjectivity concerns every section of the actual meromorphic sheaf. -/
theorem rationalMap_surjective : _root_.Function.Surjective rationalMap := by
  intro s
  obtain ⟨P, Q, _, hs⟩ := exists_polynomial_fraction s
  refine ⟨algebraMap (Polynomial ℂ) (RatFunc ℂ) P /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) Q, ?_⟩
  exact (rationalMap_apply_div P Q).trans hs.symm

/-- The rational function field is the genuine native sphere function field. -/
def rationalEquiv : RatFunc ℂ ≃ₐ[ℂ] Function 𝓘(ℂ) RiemannSphere :=
  AlgEquiv.ofBijective rationalMap ⟨rationalMap_injective, rationalMap_surjective⟩

@[simp] theorem rationalEquiv_apply (r : RatFunc ℂ) : rationalEquiv r = rationalMap r := rfl

@[simp] theorem rationalEquiv_X : rationalEquiv RatFunc.X = coordinate := rationalMap_X

/-- The intrinsic meromorphic field of the original sphere, identified
with the usual complex rational-function field. -/
def meromorphicFieldEquiv : Function 𝓘(ℂ) RiemannSphere ≃ₐ[ℂ] RatFunc ℂ :=
  rationalEquiv.symm

@[simp] theorem meromorphicFieldEquiv_coordinate :
    meromorphicFieldEquiv coordinate = RatFunc.X := by
  apply rationalEquiv.injective
  change rationalEquiv (rationalEquiv.symm coordinate) = rationalEquiv RatFunc.X
  rw [AlgEquiv.apply_symm_apply, rationalEquiv_X]

@[simp] theorem meromorphicFieldEquiv_polynomial (P : Polynomial ℂ) :
    meromorphicFieldEquiv (polynomialMap P) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) P := by
  apply rationalEquiv.injective
  change rationalEquiv (rationalEquiv.symm (polynomialMap P)) =
    rationalEquiv (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)
  rw [AlgEquiv.apply_symm_apply, rationalEquiv_apply, rationalMap_polynomial]

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative
