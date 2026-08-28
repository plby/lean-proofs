import Wikipedia.HopfProblem.ConifoldPolarDefs

/-!
# Unitary algebra in the fixed polar target coordinates

The four real normal coordinates are recovered from the original second
column.  Their quaternionic completion is unitary on the original unit sphere,
and it reconstructs every matrix fixed by the adjoint-adjugate involution.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

theorem normal_norm_sq (z : Normal) :
    ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2 + (z 3) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]

@[simp] theorem normalCoordinates_zero (M : MatrixSpace) :
    normalCoordinates M 0 = (M 0 1).re := rfl

@[simp] theorem normalCoordinates_one (M : MatrixSpace) :
    normalCoordinates M 1 = (M 0 1).im := rfl

@[simp] theorem normalCoordinates_two (M : MatrixSpace) :
    normalCoordinates M 2 = (M 1 1).re := rfl

@[simp] theorem normalCoordinates_three (M : MatrixSpace) :
    normalCoordinates M 3 = (M 1 1).im := rfl

theorem det_unitaryMatrix (z : Normal) :
    (unitaryMatrix z).det = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [normal_norm_sq]
  apply Complex.ext <;>
    simp [unitaryMatrix, Matrix.det_fin_two, pow_two] <;> ring

theorem det_unitaryMatrix_eq_one_iff (z : Normal) :
    (unitaryMatrix z).det = 1 ↔ ‖z‖ = 1 := by
  constructor
  · intro hdet
    rw [det_unitaryMatrix] at hdet
    have hsq : ‖z‖ ^ 2 = 1 := by exact_mod_cast hdet
    nlinarith [norm_nonneg z]
  · intro hz
    simp [det_unitaryMatrix, hz]

theorem adjointAdjugate_unitaryMatrix (z : Normal) :
    adjointAdjugate (unitaryMatrix z) = unitaryMatrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjointAdjugate_entries, unitaryMatrix] <;> ring

private theorem unitaryMatrix_eq_frame (z : Normal) :
    unitaryMatrix z =
      unitaryFrame ![(z 2 : ℂ) - (z 3 : ℂ) * Complex.I,
        -(z 0 : ℂ) + (z 1 : ℂ) * Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryMatrix, unitaryFrame, sub_eq_add_neg, add_comm]

private theorem unitaryMatrix_frame_norm (z : Normal) (hz : ‖z‖ = 1) :
    Complex.normSq ((z 2 : ℂ) - (z 3 : ℂ) * Complex.I) +
      Complex.normSq (-(z 0 : ℂ) + (z 1 : ℂ) * Complex.I) = 1 := by
  have h := normal_norm_sq z
  rw [hz] at h
  simp [Complex.normSq_apply]
  nlinarith

theorem unitaryMatrix_conjTranspose_mul (z : Normal) (hz : ‖z‖ = 1) :
    (unitaryMatrix z).conjTranspose * unitaryMatrix z = 1 := by
  rw [unitaryMatrix_eq_frame]
  exact unitaryFrame_conjTranspose_mul _ (unitaryMatrix_frame_norm z hz)

theorem unitaryMatrix_mul_conjTranspose (z : Normal) (hz : ‖z‖ = 1) :
    unitaryMatrix z * (unitaryMatrix z).conjTranspose = 1 := by
  rw [unitaryMatrix_eq_frame]
  exact unitaryFrame_mul_conjTranspose _ (unitaryMatrix_frame_norm z hz)

@[simp] theorem normalCoordinates_unitaryMatrix (z : Normal) :
    normalCoordinates (unitaryMatrix z) = z := by
  ext i
  fin_cases i <;> simp [unitaryMatrix]

theorem unitaryMatrix_normalCoordinates (M : MatrixSpace)
    (h : adjointAdjugate M = M) :
    unitaryMatrix (normalCoordinates M) = M := by
  have h00 : conj (M 1 1) = M 0 0 := by
    simpa [adjointAdjugate_entries] using congrArg (fun N : MatrixSpace => N 0 0) h
  have h10 : -conj (M 0 1) = M 1 0 := by
    simpa [adjointAdjugate_entries] using congrArg (fun N : MatrixSpace => N 1 0) h
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [unitaryMatrix, ← h00, ← h10]

theorem norm_normalCoordinates_eq_one (M : MatrixSpace)
    (h : adjointAdjugate M = M) (hdet : M.det = 1) :
    ‖normalCoordinates M‖ = 1 := by
  apply (det_unitaryMatrix_eq_one_iff _).mp
  rw [unitaryMatrix_normalCoordinates M h, hdet]

end Wikipedia.HopfProblem.ConifoldPolar
