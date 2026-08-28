import Wikipedia.HopfProblem.CanonicalBundleAlternating
import Wikipedia.HopfProblem.PeriodTori

/-!
# Continuous top covectors on the period-family model

The existing period-family atlas has model `ℂ × (Fin 2 → ℂ)`.  Its canonical
line is therefore the line of continuous alternating three-covectors on this
product, not on a replacement chart model.  The coordinate equivalence used
below only identifies its standard volume with `dz ∧ dζ₀ ∧ dζ₁`.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

abbrev Model := ℂ × ComplexPlane₂

abbrev TopCovector := Model [⋀^(Fin 3)]→L[ℂ] ℂ

/-- Base coordinate first, followed by the two fibre coordinates. -/
def coordinateEquiv : Model ≃L[ℂ] CanonicalBundle.Model :=
  Fin.consEquivL ℂ (fun _ : Fin 3 => ℂ)

@[simp] theorem coordinateEquiv_apply (x : Model) :
    coordinateEquiv x = ![x.1, x.2 0, x.2 1] := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem coordinateEquiv_symm_apply (x : CanonicalBundle.Model) :
    coordinateEquiv.symm x = (x 0, ![x 1, x 2]) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

/-- The genuine basis of the product vector space, in base-first order. -/
def basis : Module.Basis (Fin 3) ℂ Model :=
  (Pi.basisFun ℂ (Fin 3)).map coordinateEquiv.symm.toLinearEquiv

@[simp] theorem basis_repr (x : Model) (i : Fin 3) :
    basis.repr x i = coordinateEquiv x i := by
  simp [basis]

/-- The standard volume form on the actual product model. -/
def volume : TopCovector :=
  CanonicalBundle.volume.compContinuousLinearMap coordinateEquiv.toContinuousLinearMap

@[simp] theorem volume_apply (v : Fin 3 → Model) :
    volume v = (Matrix.of (fun i => coordinateEquiv (v i))).det :=
  CanonicalBundle.volume_apply _

theorem volume_toAlternatingMap : volume.toAlternatingMap = basis.det := by
  ext v
  change CanonicalBundle.volume (coordinateEquiv ∘ v) = basis.det v
  rw [basis, Module.Basis.det_map]
  rfl

@[simp] theorem volume_basis : volume basis = 1 := by
  change volume.toAlternatingMap basis = 1
  rw [volume_toAlternatingMap]
  exact basis.det_self

/-- Scalar coefficient of a genuine top covector in the standard volume. -/
def coefficient (α : TopCovector) : ℂ := α basis

theorem eq_coefficient_smul_volume (α : TopCovector) :
    α = coefficient α • volume := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change α.toAlternatingMap = coefficient α • volume.toAlternatingMap
  rw [volume_toAlternatingMap]
  exact α.toAlternatingMap.eq_smul_basis_det basis

@[simp] theorem coefficient_volume : coefficient volume = 1 := volume_basis

@[simp] theorem coefficient_smul (c : ℂ) (α : TopCovector) :
    coefficient (c • α) = c * coefficient α := rfl

@[simp] theorem coefficient_zero : coefficient 0 = 0 := rfl

theorem volume_ne_zero : volume ≠ 0 := by
  intro h
  have he := congrArg coefficient h
  simp at he

/-- The continuous linear coefficient equivalence for the product model. -/
def coefficientEquiv : ℂ ≃L[ℂ] TopCovector where
  toFun c := c • volume
  invFun := coefficient
  left_inv c := by simp
  right_inv α := (eq_coefficient_smul_volume α).symm
  map_add' c d := add_smul c d volume
  map_smul' c d := (smul_smul c d volume).symm
  continuous_toFun := continuous_id.smul continuous_const
  continuous_invFun := continuous_eval_const (basis : Fin 3 → Model)

@[simp] theorem coefficientEquiv_apply (c : ℂ) :
    coefficientEquiv c = c • volume := rfl

@[simp] theorem coefficientEquiv_symm_apply (α : TopCovector) :
    coefficientEquiv.symm α = coefficient α := rfl

theorem coefficient_eq_zero_iff (α : TopCovector) :
    coefficient α = 0 ↔ α = 0 := coefficientEquiv.symm.map_eq_zero_iff

/-- Pulling back the volume by an actual endomorphism of the product model. -/
theorem volume_pullback (A : Model →L[ℂ] Model) :
    volume.compContinuousLinearMap A = LinearMap.det A.toLinearMap • volume := by
  ext v
  change volume.toAlternatingMap (A ∘ v) =
    LinearMap.det A.toLinearMap * volume.toAlternatingMap v
  rw [volume_toAlternatingMap]
  exact basis.det_comp A.toLinearMap v

theorem coefficient_pullback (α : TopCovector) (A : Model →L[ℂ] Model) :
    coefficient (α.compContinuousLinearMap A) =
      LinearMap.det A.toLinearMap * coefficient α := by
  rw [eq_coefficient_smul_volume α]
  change coefficient α * volume.toAlternatingMap (A ∘ basis) =
    LinearMap.det A.toLinearMap *
      (coefficient α * volume.toAlternatingMap basis)
  rw [volume_toAlternatingMap]
  have h : basis.det (A ∘ (basis : Fin 3 → Model)) =
      LinearMap.det A.toLinearMap * basis.det basis :=
    basis.det_comp A.toLinearMap (basis : Fin 3 → Model)
  rw [h]
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

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
