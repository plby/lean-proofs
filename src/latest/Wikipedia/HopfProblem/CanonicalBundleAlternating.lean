import Wikipedia.HopfProblem.ToricCharts
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix

/-!
# The line of continuous top alternating covectors

The standard determinant is a continuous alternating covector on `ℂ³`.
Every top covector has a unique scalar coefficient relative to it. Pullback
by a continuous linear map multiplies this coefficient by its determinant.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CanonicalBundle

open ToricCharts

abbrev Model := CoordinateSpace 3

abbrev TopCovector := Model [⋀^(Fin 3)]→L[ℂ] ℂ

def volume : TopCovector :=
  { (Pi.basisFun ℂ (Fin 3)).det with
    cont := by
      change Continuous (fun v : Fin 3 → Model => (Pi.basisFun ℂ (Fin 3)).det v)
      convert! (continuous_id :
        Continuous (fun v : Matrix (Fin 3) (Fin 3) ℂ => v)).matrix_det using 1
      ext v
      exact Pi.basisFun_det_apply v }

@[simp] theorem volume_apply (v : Fin 3 → Model) : volume v = (Matrix.of v).det :=
  Pi.basisFun_det_apply v

@[simp] theorem volume_basis : volume (Pi.basisFun ℂ (Fin 3)) = 1 :=
  (Pi.basisFun ℂ (Fin 3)).det_self

def coefficient (α : TopCovector) : ℂ := α (Pi.basisFun ℂ (Fin 3))

theorem eq_coefficient_smul_volume (α : TopCovector) : α = coefficient α • volume := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact α.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin 3))

@[simp] theorem coefficient_volume : coefficient volume = 1 := volume_basis

@[simp] theorem coefficient_smul (c : ℂ) (α : TopCovector) :
    coefficient (c • α) = c * coefficient α := rfl

@[simp] theorem coefficient_zero : coefficient 0 = 0 := rfl

theorem volume_ne_zero : volume ≠ 0 := by
  intro h
  have he := congrArg coefficient h
  simp at he

def coefficientEquiv : ℂ ≃L[ℂ] TopCovector where
  toFun c := c • volume
  invFun := coefficient
  left_inv c := by simp
  right_inv α := (eq_coefficient_smul_volume α).symm
  map_add' c d := add_smul c d volume
  map_smul' c d := (smul_smul c d volume).symm
  continuous_toFun := continuous_id.smul continuous_const
  continuous_invFun := by
    change Continuous (fun α : TopCovector => α (Pi.basisFun ℂ (Fin 3)))
    exact continuous_eval_const ((Pi.basisFun ℂ (Fin 3)) : Fin 3 → Model)

@[simp] theorem coefficientEquiv_apply (c : ℂ) : coefficientEquiv c = c • volume := rfl

@[simp] theorem coefficientEquiv_symm_apply (α : TopCovector) :
    coefficientEquiv.symm α = coefficient α := rfl

theorem coefficient_eq_zero_iff (α : TopCovector) : coefficient α = 0 ↔ α = 0 :=
  coefficientEquiv.symm.map_eq_zero_iff

theorem volume_pullback (A : Model →L[ℂ] Model) :
    volume.compContinuousLinearMap A = LinearMap.det A.toLinearMap • volume := by
  ext v
  exact (Pi.basisFun ℂ (Fin 3)).det_comp A.toLinearMap v

theorem coefficient_pullback (α : TopCovector) (A : Model →L[ℂ] Model) :
    coefficient (α.compContinuousLinearMap A) =
      LinearMap.det A.toLinearMap * coefficient α := by
  rw [eq_coefficient_smul_volume α]
  change (coefficient α * volume (A ∘ (Pi.basisFun ℂ (Fin 3)))) =
    LinearMap.det A.toLinearMap * (coefficient α * volume (Pi.basisFun ℂ (Fin 3)))
  change (coefficient α * (Pi.basisFun ℂ (Fin 3)).det
      (A.toLinearMap ∘ (Pi.basisFun ℂ (Fin 3)))) = _
  rw [Module.Basis.det_comp]
  change coefficient α * (LinearMap.det A.toLinearMap * volume (Pi.basisFun ℂ (Fin 3))) = _
  ring

theorem pullback_eq_det_smul (α : TopCovector) (A : Model →L[ℂ] Model) :
    α.compContinuousLinearMap A = LinearMap.det A.toLinearMap • α := by
  apply coefficientEquiv.symm.injective
  exact coefficient_pullback α A

theorem coefficientEquiv_pullback (c : ℂ) (A : Model →L[ℂ] Model) :
    (coefficientEquiv c).compContinuousLinearMap A =
      coefficientEquiv (LinearMap.det A.toLinearMap * c) := by
  rw [pullback_eq_det_smul]
  simp [mul_smul]

end Wikipedia.HopfProblem.CanonicalBundle
