import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.StdBasis

/-!
# Integer dual coordinates for finite free modules

The standard basis identifies the integer dual of `ℤʳ` with `ℤʳ` by
evaluation.  Transporting this identification along an explicit linear
equivalence gives coordinate and evaluation formulas on any finite free
integer module, with naturality under a coordinate-preserving map.

This file contains only linear algebra and assumes no cohomology or
universal-coefficient comparison.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- Integer dual coordinates are the coefficients in the standard dual basis. -/
def intDualCoordinates (r : ℕ) :
    ((Fin r → ℤ) →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (Fin r → ℤ) :=
  (Pi.basisFun ℤ (Fin r)).dualBasis.equivFun

@[simp] theorem intDualCoordinates_apply (r : ℕ)
    (φ : (Fin r → ℤ) →ₗ[ℤ] ℤ) (i : Fin r) :
    intDualCoordinates r φ i = φ (Pi.single i 1) := by
  rw [intDualCoordinates, Module.Basis.dualBasis_equivFun, Pi.basisFun_apply]

@[simp] theorem intDualCoordinates_symm_apply (r : ℕ) (a x : Fin r → ℤ) :
    (intDualCoordinates r).symm a x = ∑ i, a i * x i := by
  change (Pi.basisFun ℤ (Fin r)).dualBasis.equivFun.symm a x = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.dualBasis_apply, Pi.basisFun_repr]

theorem intDualCoordinates_evaluate (r : ℕ) (φ : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (x : Fin r → ℤ) :
    φ x = ∑ i, intDualCoordinates r φ i * x i := by
  simpa only [LinearEquiv.symm_apply_apply] using
    intDualCoordinates_symm_apply r (intDualCoordinates r φ) x

variable {r : ℕ} {M N : Type*} [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N]

/-- Dual coordinates transported by precomposition with the inverse coordinate equivalence. -/
def intDualCoordinatesOfEquiv (e : M ≃ₗ[ℤ] (Fin r → ℤ)) :
    (M →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (Fin r → ℤ) :=
  e.symm.dualMap.trans (intDualCoordinates r)

@[simp] theorem intDualCoordinatesOfEquiv_apply (e : M ≃ₗ[ℤ] (Fin r → ℤ))
    (φ : M →ₗ[ℤ] ℤ) (i : Fin r) :
    intDualCoordinatesOfEquiv e φ i = φ (e.symm (Pi.single i 1)) := by
  rw [intDualCoordinatesOfEquiv, LinearEquiv.trans_apply, intDualCoordinates_apply,
    LinearEquiv.dualMap_apply]

@[simp] theorem intDualCoordinatesOfEquiv_symm_apply (e : M ≃ₗ[ℤ] (Fin r → ℤ))
    (a : Fin r → ℤ) (x : M) :
    (intDualCoordinatesOfEquiv e).symm a x = ∑ i, a i * e x i := by
  change (intDualCoordinates r).symm a (e x) = _
  exact intDualCoordinates_symm_apply r a (e x)

/-- Evaluation is the integer coordinate pairing. -/
theorem intDualCoordinatesOfEquiv_evaluate (e : M ≃ₗ[ℤ] (Fin r → ℤ))
    (φ : M →ₗ[ℤ] ℤ) (x : M) :
    φ x = ∑ i, intDualCoordinatesOfEquiv e φ i * e x i := by
  simpa only [LinearEquiv.symm_apply_apply] using
    intDualCoordinatesOfEquiv_symm_apply e (intDualCoordinatesOfEquiv e φ) x

/-- Pullback preserves dual coordinates when the original map preserves coordinates. -/
theorem intDualCoordinatesOfEquiv_naturality (L : M →ₗ[ℤ] N)
    (eM : M ≃ₗ[ℤ] (Fin r → ℤ)) (eN : N ≃ₗ[ℤ] (Fin r → ℤ))
    (hL : ∀ x, eN (L x) = eM x) (φ : N →ₗ[ℤ] ℤ) :
    intDualCoordinatesOfEquiv eM (φ.comp L) = intDualCoordinatesOfEquiv eN φ := by
  funext i
  rw [intDualCoordinatesOfEquiv_apply, intDualCoordinatesOfEquiv_apply,
    LinearMap.comp_apply]
  congr 1
  apply eN.injective
  rw [hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem intDualCoordinatesOfEquiv_naturality_linearMap (L : M →ₗ[ℤ] N)
    (eM : M ≃ₗ[ℤ] (Fin r → ℤ)) (eN : N ≃ₗ[ℤ] (Fin r → ℤ))
    (hL : ∀ x, eN (L x) = eM x) :
    (intDualCoordinatesOfEquiv eM).toLinearMap.comp L.dualMap =
      (intDualCoordinatesOfEquiv eN).toLinearMap := by
  apply LinearMap.ext
  intro φ
  exact intDualCoordinatesOfEquiv_naturality L eM eN hL φ

end Wikipedia.HopfProblem.Elliptic.HigherHomology
