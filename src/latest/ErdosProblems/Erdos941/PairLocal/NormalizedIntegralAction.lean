/- Adapted from the checked repository proof in Erdos1148/NormalizedIntegralAction.lean. -/
import ErdosProblems.Erdos941.PairLocal.NormalizedAction
import ErdosProblems.Erdos941.PairLocal.CoefficientLattices

/-!
# Unimodular changes of lattice representatives

The normalized action of a matrix with unit determinant is integral.
Left multiplication of a projective matrix by such a matrix therefore
does not change the image of the standard coefficient lattice.
-/

namespace Erdos941.PairLocal

lemma transformMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) :
    transformMatrix (A.map φ) = (transformMatrix A).map φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transformMatrix, map_ofNat]

lemma normalizedTransformIsometry_mul {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    normalizedTransformIsometry (A * B) (by rw [Matrix.det_mul]; exact mul_ne_zero hA hB) =
      normalizedTransformIsometry B hB * normalizedTransformIsometry A hA := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro t
  change (normalizedTransformIsometry (A * B) _).1 t =
    (normalizedTransformIsometry B hB).1 ((normalizedTransformIsometry A hA).1 t)
  rw [normalizedTransformIsometry_apply, normalizedTransformIsometry_apply,
    normalizedTransformIsometry_apply, transform_mul, Matrix.det_mul, mul_inv_rev]
  change (B.det⁻¹ * A.det⁻¹) • transform B (transform A t) =
    B.det⁻¹ • (transformLinear B) (A.det⁻¹ • transform A t)
  rw [map_smul, smul_smul]
  rfl

lemma exists_integral_normalized_transform {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) (A : Matrix (Fin 2) (Fin 2) R)
    (hA : IsUnit A.det) (hAK : (A.map φ).det ≠ 0) :
    ∃ k : specialDiscrGroup R,
      specialDiscrBaseChange φ k = normalizedTransformIsometry (A.map φ) hAK := by
  let u := hA.unit
  have hu : (u : R) = A.det := hA.unit_spec
  have hdet : (A.map φ).det = φ A.det := (φ.map_det A).symm
  have hinv : φ (↑u⁻¹ : R) = (φ A.det)⁻¹ := by
    have h : φ (↑u⁻¹ : R) * φ A.det = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    exact eq_inv_of_mul_eq_one_left h
  let M : Matrix (Fin 3) (Fin 3) R := (↑u⁻¹ : R) • transformMatrix A
  have hM : M.map φ = normalizedTransformMatrix (A.map φ) := by
    rw [normalizedTransformMatrix, hdet, transformMatrix_map]
    ext i j
    change φ ((↑u⁻¹ : R) * transformMatrix A i j) =
      (φ A.det)⁻¹ * φ (transformMatrix A i j)
    rw [map_mul, hinv]
  apply exists_specialDiscrGroup_of_matrix φ hφ _ M
  change M.map φ = matrixOfCoeffMap
    (coeffMatrixEquiv (normalizedTransformMatrix (A.map φ)) _).toLinearMap
  rw [coeffMatrixEquiv_toLinearMap, matrixOfCoeffMap_coeffMatrixMap, hM]

lemma mem_integralCoeffSet_baseChange_symm_iff {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (k : specialDiscrGroup R) (t : K × K × K) :
    (specialDiscrBaseChange φ k).1.symm t ∈ integralCoeffSet φ ↔ t ∈ integralCoeffSet φ := by
  have h := mem_integralCoeffSet_baseChange_iff φ k ((specialDiscrBaseChange φ k).1.symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

lemma coefficientLattice_inv_mul_baseChange {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (k : specialDiscrGroup R) (g : specialDiscrGroup K) :
    coefficientLattice φ (g * specialDiscrBaseChange φ k)⁻¹ = coefficientLattice φ g⁻¹ := by
  rw [mul_inv_rev]
  ext t
  exact mem_integralCoeffSet_baseChange_symm_iff φ k (g.1.symm t)

lemma image_lattice_normalized_left_unit {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ)
    (U : Matrix (Fin 2) (Fin 2) R) (hU : IsUnit U.det)
    (hUK : (U.map φ).det ≠ 0) (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det ≠ 0) :
    coefficientLattice φ (normalizedTransformIsometry (U.map φ * A)
      (by rw [Matrix.det_mul]; exact mul_ne_zero hUK hA))⁻¹ =
      coefficientLattice φ (normalizedTransformIsometry A hA)⁻¹ := by
  obtain ⟨k, hk⟩ := exists_integral_normalized_transform φ hφ U hU hUK
  rw [normalizedTransformIsometry_mul (U.map φ) A hUK hA, ← hk]
  exact coefficientLattice_inv_mul_baseChange φ k _

end Erdos941.PairLocal
