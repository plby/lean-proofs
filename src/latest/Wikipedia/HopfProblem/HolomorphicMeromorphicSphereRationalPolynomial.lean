import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereCoordinate
import Wikipedia.HopfProblem.HolomorphicMeromorphicAlgebraMaps
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomials in the native meromorphic coordinate

Evaluation at the actual meromorphic coordinate is injective. The proof
compares the literal restrictions to the finite chart, where they are
the original holomorphic polynomial functions and have their usual values.
There is no pointwise evaluation homomorphism at a meromorphic pole.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative

open RiemannSphere HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- Evaluate a polynomial in the genuine global meromorphic coordinate. -/
def polynomialMap : Polynomial ℂ →ₐ[ℂ] Function 𝓘(ℂ) RiemannSphere :=
  Polynomial.aeval coordinate

@[simp] theorem polynomialMap_X : polynomialMap Polynomial.X = coordinate :=
  Polynomial.aeval_X coordinate

@[simp] theorem polynomialMap_C (c : ℂ) :
    polynomialMap (Polynomial.C c) = algebraMap ℂ (Function 𝓘(ℂ) RiemannSphere) c :=
  Polynomial.aeval_C coordinate c

/-- The actual restriction map intertwines polynomial evaluation with
the genuine holomorphic inclusion on the original finite chart. -/
theorem polynomialMap_restriction :
    (restrictionAlgHom 𝓘(ℂ) RiemannSphere (le_top : finiteChart ≤ ⊤)).comp polynomialMap =
      (ofHolomorphicAlgHom 𝓘(ℂ) RiemannSphere finiteChart).comp
        (Polynomial.aeval finiteCoordinate) := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply, polynomialMap_X, Polynomial.aeval_X,
    restrictionAlgHom_apply, ofHolomorphicAlgHom_apply, coordinate_restrict_finite]

theorem polynomialMap_restrict_finite (P : Polynomial ℂ) :
    restrict 𝓘(ℂ) RiemannSphere (le_top : finiteChart ≤ ⊤) (polynomialMap P) =
      ofHolomorphic 𝓘(ℂ) RiemannSphere finiteChart (Polynomial.aeval finiteCoordinate P) :=
  AlgHom.congr_fun polynomialMap_restriction P

/-- Ordinary evaluation of genuine holomorphic functions in this chart. -/
def finiteHolomorphicEvaluation (z : ℂ) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere finiteChart →ₐ[ℂ] ℂ where
  __ := ContMDiffMap.evalRingHom ⟨(z : RiemannSphere), coe_mem_finiteChart z⟩
  commutes' _ := rfl

theorem finite_polynomial_value (P : Polynomial ℂ) (z : ℂ) :
    (Polynomial.aeval finiteCoordinate P)
      ⟨(z : RiemannSphere), coe_mem_finiteChart z⟩ = P.eval z := by
  change finiteHolomorphicEvaluation z (Polynomial.aeval finiteCoordinate P) = P.eval z
  rw [← Polynomial.aeval_algHom_apply]
  rfl

/-- Polynomial sections are regular at every finite point, with exactly
their ordinary polynomial values. -/
@[simp] theorem polynomialMap_finiteValue (P : Polynomial ℂ) (z : ℂ) :
    SphereRepresentative.finiteValue (polynomialMap P) z = P.eval z := by
  let y : finiteChart := ⟨(z : RiemannSphere), coe_mem_finiteChart z⟩
  have hv := value_restrict 𝓘(ℂ) RiemannSphere (le_top : finiteChart ≤ ⊤)
    (polynomialMap P) y
  rw [polynomialMap_restrict_finite, value_ofHolomorphic] at hv
  exact hv.symm.trans (finite_polynomial_value P z)

/-- No nonzero polynomial vanishes in the actual meromorphic field. -/
theorem polynomialMap_injective : _root_.Function.Injective polynomialMap := by
  intro P Q h
  apply Polynomial.funext
  intro z
  have hv := congrArg (fun s => SphereRepresentative.finiteValue s z) h
  simpa only [polynomialMap_finiteValue] using hv

@[simp] theorem polynomialMap_eq_zero_iff (P : Polynomial ℂ) :
    polynomialMap P = 0 ↔ P = 0 :=
  map_eq_zero_iff polynomialMap polynomialMap_injective

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative
