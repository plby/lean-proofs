import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix

/-!
# Continuous alternating two-covectors on the elliptic surface model

The determinant is an element of the full space of continuous alternating
two-covectors on `ComplexPlane₂`. Every such covector has a unique scalar
coefficient. Pullback by an actual continuous linear map multiplies that
coefficient by the map's determinant.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.CanonicalBundle

abbrev Model := ComplexPlane₂

abbrev TopCovector := Model [⋀^(Fin 2)]→L[ℂ] ℂ

def volume : TopCovector :=
  { (Pi.basisFun ℂ (Fin 2)).det with
    cont := by
      change Continuous (fun v : Fin 2 → Model => (Pi.basisFun ℂ (Fin 2)).det v)
      convert! (continuous_id :
        Continuous (fun v : Matrix (Fin 2) (Fin 2) ℂ => v)).matrix_det using 1
      ext v
      exact Pi.basisFun_det_apply v }

@[simp] theorem volume_apply (v : Fin 2 → Model) : volume v = (Matrix.of v).det :=
  Pi.basisFun_det_apply v

@[simp] theorem volume_basis : volume (Pi.basisFun ℂ (Fin 2)) = 1 :=
  (Pi.basisFun ℂ (Fin 2)).det_self

def coefficient (α : TopCovector) : ℂ := α (Pi.basisFun ℂ (Fin 2))

theorem eq_coefficient_smul_volume (α : TopCovector) : α = coefficient α • volume := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact α.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin 2))

@[simp] theorem coefficient_volume : coefficient volume = 1 := volume_basis

@[simp] theorem coefficient_smul (c : ℂ) (α : TopCovector) :
    coefficient (c • α) = c * coefficient α := rfl

@[simp] theorem coefficient_zero : coefficient 0 = 0 := rfl

theorem volume_ne_zero : volume ≠ 0 := by
  intro h
  have he := congrArg coefficient h
  simp at he

/-- A continuous complex-linear equivalence with the entire space of
alternating two-covectors, rather than with a selected subspace of forms. -/
def coefficientEquiv : ℂ ≃L[ℂ] TopCovector where
  toFun c := c • volume
  invFun := coefficient
  left_inv c := by simp
  right_inv α := (eq_coefficient_smul_volume α).symm
  map_add' c d := add_smul c d volume
  map_smul' c d := (smul_smul c d volume).symm
  continuous_toFun := continuous_id.smul continuous_const
  continuous_invFun := by
    change Continuous (fun α : TopCovector => α (Pi.basisFun ℂ (Fin 2)))
    exact continuous_eval_const ((Pi.basisFun ℂ (Fin 2)) : Fin 2 → Model)

@[simp] theorem coefficientEquiv_apply (c : ℂ) : coefficientEquiv c = c • volume := rfl

@[simp] theorem coefficientEquiv_symm_apply (α : TopCovector) :
    coefficientEquiv.symm α = coefficient α := rfl

theorem coefficient_eq_zero_iff (α : TopCovector) : coefficient α = 0 ↔ α = 0 :=
  coefficientEquiv.symm.map_eq_zero_iff

theorem topCovector_rank_one : Module.finrank ℂ TopCovector = 1 := by
  rw [← coefficientEquiv.toLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

theorem volume_pullback (L : Model →L[ℂ] Model) :
    volume.compContinuousLinearMap L = LinearMap.det L.toLinearMap • volume := by
  ext v
  exact (Pi.basisFun ℂ (Fin 2)).det_comp L.toLinearMap v

theorem coefficient_pullback (α : TopCovector) (L : Model →L[ℂ] Model) :
    coefficient (α.compContinuousLinearMap L) =
      LinearMap.det L.toLinearMap * coefficient α := by
  rw [eq_coefficient_smul_volume α]
  change (coefficient α * volume (L ∘ (Pi.basisFun ℂ (Fin 2)))) =
    LinearMap.det L.toLinearMap * (coefficient α * volume (Pi.basisFun ℂ (Fin 2)))
  change (coefficient α * (Pi.basisFun ℂ (Fin 2)).det
      (L.toLinearMap ∘ (Pi.basisFun ℂ (Fin 2)))) = _
  rw [Module.Basis.det_comp]
  change coefficient α * (LinearMap.det L.toLinearMap * volume (Pi.basisFun ℂ (Fin 2))) = _
  ring

theorem pullback_eq_det_smul (α : TopCovector) (L : Model →L[ℂ] Model) :
    α.compContinuousLinearMap L = LinearMap.det L.toLinearMap • α := by
  apply coefficientEquiv.symm.injective
  exact coefficient_pullback α L

theorem coefficientEquiv_pullback (c : ℂ) (L : Model →L[ℂ] Model) :
    (coefficientEquiv c).compContinuousLinearMap L =
      coefficientEquiv (LinearMap.det L.toLinearMap * c) := by
  rw [pullback_eq_det_smul]
  simp [mul_smul]

end Wikipedia.HopfProblem.Elliptic.CanonicalBundle
