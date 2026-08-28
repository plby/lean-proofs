import Wikipedia.HopfProblem.EllipticHigherHomologyAlgebraDegreeOne
import Wikipedia.HopfProblem.EllipticHigherHomologyAlgebraDegreeTwo

/-!
# The inverse-monodromy convention over the integers

The operators `1 - B⁻¹` and `B - 1` have exactly the same kernel and image
for an invertible integral matrix.  The same statement applies to the
actual exterior-square matrices.  Thus the explicit integral coordinates
remain valid in the inverse-monodromy convention.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

theorem matrixInverseDifference_mul (M : FibreMatrix) (hM : IsUnit M.det) :
    (1 - M⁻¹) * M = M - 1 := by
  rw [sub_mul, one_mul, Matrix.nonsing_inv_mul M hM]

theorem mul_matrixInverseDifference (M : FibreMatrix) (hM : IsUnit M.det) :
    M * (1 - M⁻¹) = M - 1 := by
  rw [mul_sub, mul_one, Matrix.mul_nonsing_inv M hM]

theorem matrixInverseDifference_ker_eq (M : FibreMatrix) (hM : IsUnit M.det) :
    LinearMap.ker (1 - M⁻¹).mulVecLin = LinearMap.ker (M - 1).mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro hv
    have h := congrArg (fun w : FibreLattice => M *ᵥ w) hv
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM,
      Matrix.one_mulVec] using h
  · intro hv
    have h := congrArg (fun w : FibreLattice => M⁻¹ *ᵥ w) hv
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM,
      Matrix.one_mulVec] using h

theorem matrixInverseDifference_range_eq (M : FibreMatrix) (hM : IsUnit M.det) :
    LinearMap.range (1 - M⁻¹).mulVecLin = LinearMap.range (M - 1).mulVecLin := by
  ext v
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨M⁻¹ *ᵥ w, ?_⟩
    change (M - 1) *ᵥ M⁻¹ *ᵥ w = v
    rw [Matrix.mulVec_mulVec, sub_mul, Matrix.mul_nonsing_inv M hM, one_mul]
    exact hw
  · rintro ⟨w, hw⟩
    refine ⟨M *ᵥ w, ?_⟩
    change (1 - M⁻¹) *ᵥ M *ᵥ w = v
    rw [Matrix.mulVec_mulVec, matrixInverseDifference_mul M hM]
    exact hw

/-- The actual degree-one difference in the inverse convention. -/
def fibreInverseDifference (j : Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (1 - (fibreMatrix j)⁻¹).mulVecLin

/-- The actual degree-two difference in the inverse convention. -/
def fibreSquareInverseDifference (j : Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (1 - (fibreSquareMatrix j)⁻¹).mulVecLin

theorem fibreInverseDifference_comp_monodromy (j : Kind) :
    (fibreInverseDifference j).comp (fibreMatrix j).mulVecLin = fibreDifference j := by
  rw [fibreInverseDifference, ← Matrix.mulVecLin_mul,
    matrixInverseDifference_mul _ (by simp [fibreMatrix_det])]
  rfl

theorem monodromy_comp_fibreInverseDifference (j : Kind) :
    (fibreMatrix j).mulVecLin.comp (fibreInverseDifference j) = fibreDifference j := by
  rw [fibreInverseDifference, ← Matrix.mulVecLin_mul,
    mul_matrixInverseDifference _ (by simp [fibreMatrix_det])]
  rfl

theorem fibreSquareInverseDifference_comp_monodromy (j : Kind) :
    (fibreSquareInverseDifference j).comp (fibreSquareMatrix j).mulVecLin =
      fibreSquareDifference j := by
  rw [fibreSquareInverseDifference, ← Matrix.mulVecLin_mul,
    matrixInverseDifference_mul _ (by simp [fibreSquareMatrix_det])]
  rfl

theorem monodromy_comp_fibreSquareInverseDifference (j : Kind) :
    (fibreSquareMatrix j).mulVecLin.comp (fibreSquareInverseDifference j) =
      fibreSquareDifference j := by
  rw [fibreSquareInverseDifference, ← Matrix.mulVecLin_mul,
    mul_matrixInverseDifference _ (by simp [fibreSquareMatrix_det])]
  rfl

theorem fibreInverseDifference_ker_eq (j : Kind) :
    LinearMap.ker (fibreInverseDifference j) = LinearMap.ker (fibreDifference j) :=
  matrixInverseDifference_ker_eq _ (by simp [fibreMatrix_det])

theorem fibreInverseDifference_range_eq (j : Kind) :
    LinearMap.range (fibreInverseDifference j) = LinearMap.range (fibreDifference j) :=
  matrixInverseDifference_range_eq _ (by simp [fibreMatrix_det])

theorem fibreSquareInverseDifference_ker_eq (j : Kind) :
    LinearMap.ker (fibreSquareInverseDifference j) =
      LinearMap.ker (fibreSquareDifference j) :=
  matrixInverseDifference_ker_eq _ (by simp [fibreSquareMatrix_det])

theorem fibreSquareInverseDifference_range_eq (j : Kind) :
    LinearMap.range (fibreSquareInverseDifference j) =
      LinearMap.range (fibreSquareDifference j) :=
  matrixInverseDifference_range_eq _ (by simp [fibreSquareMatrix_det])

/-- Integral invariants in the degree-one inverse convention. -/
def fibreInverseKernelEquivInt (j : Kind) :
    LinearMap.ker (fibreInverseDifference j) ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofEq _ _ (fibreInverseDifference_ker_eq j)).trans (fibreKernelEquivInt j)

@[simp] theorem fibreInverseKernelEquivInt_apply (j : Kind)
    (v : LinearMap.ker (fibreInverseDifference j)) :
    fibreInverseKernelEquivInt j v = (v : FibreLattice) 2 := rfl

@[simp] theorem fibreInverseKernelEquivInt_symm_apply (j : Kind) (k : ℤ) :
    ((fibreInverseKernelEquivInt j).symm k : FibreLattice) = ![0, 0, k] := rfl

/-- Integral coinvariants in the degree-one inverse convention. -/
def fibreInverseCokernelEquivInt (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreInverseDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreInverseDifference_range_eq j)).trans
    (fibreCokernelEquivInt j)

@[simp] theorem fibreInverseCokernelEquivInt_apply_mk (j : Kind) (v : FibreLattice) :
    fibreInverseCokernelEquivInt j (Submodule.Quotient.mk v) =
      fibreCoinvariantCoordinate j v := rfl

@[simp] theorem fibreInverseCokernelEquivInt_symm_apply (j : Kind) (k : ℤ) :
    (fibreInverseCokernelEquivInt j).symm k = Submodule.Quotient.mk ![0, k, 0] := by
  apply (fibreInverseCokernelEquivInt j).injective
  simp

/-- Integral invariants in the degree-two inverse convention. -/
def fibreSquareInverseKernelEquivInt (j : Kind) :
    LinearMap.ker (fibreSquareInverseDifference j) ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofEq _ _ (fibreSquareInverseDifference_ker_eq j)).trans
    (fibreSquareKernelEquivInt j)

@[simp] theorem fibreSquareInverseKernelEquivInt_apply (j : Kind)
    (v : LinearMap.ker (fibreSquareInverseDifference j)) :
    fibreSquareInverseKernelEquivInt j v = -(v : FibreLattice) 1 := rfl

@[simp] theorem fibreSquareInverseKernelEquivInt_symm_apply (j : Kind) (k : ℤ) :
    ((fibreSquareInverseKernelEquivInt j).symm k : FibreLattice) =
      k • fibreSquareKernelVector j := rfl

/-- Integral coinvariants in the degree-two inverse convention. -/
def fibreSquareInverseCokernelEquivInt (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreSquareInverseDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreSquareInverseDifference_range_eq j)).trans
    (fibreSquareCokernelEquivInt j)

@[simp] theorem fibreSquareInverseCokernelEquivInt_apply_mk (j : Kind) (v : FibreLattice) :
    fibreSquareInverseCokernelEquivInt j (Submodule.Quotient.mk v) = v 0 := rfl

@[simp] theorem fibreSquareInverseCokernelEquivInt_symm_apply (j : Kind) (k : ℤ) :
    (fibreSquareInverseCokernelEquivInt j).symm k = Submodule.Quotient.mk ![k, 0, 0] := by
  apply (fibreSquareInverseCokernelEquivInt j).injective
  simp

end Wikipedia.HopfProblem.Elliptic.HigherHomology
