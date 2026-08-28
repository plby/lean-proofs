import Wikipedia.HopfProblem.EllipticHigherHomologyData

/-!
# Integral coordinates along the actual elliptic twist

The columns of the change-of-basis matrix are the chosen primitive
twist and the last three standard basis vectors.  Its inverse is
integral, and conjugation of the actual elliptic matrix splits off the
fixed twist direction from the three-dimensional fibre action.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The integral basis with columns `(j.twist, e₁, e₂, e₃)`. -/
def twistBasisMatrix : Kind → LatticeMatrix
  | .three => !![1, 0, 0, 0; 2, 1, 0, 0; -4, 0, 1, 0; 0, 0, 0, 1]
  | .four => !![-1, 0, 0, 0; -3, 1, 0, 0; 3, 0, 1, 0; 0, 0, 0, 1]

/-- The explicit integral inverse of the twist basis. -/
def twistBasisInvMatrix : Kind → LatticeMatrix
  | .three => !![1, 0, 0, 0; -2, 1, 0, 0; 4, 0, 1, 0; 0, 0, 0, 1]
  | .four => !![-1, 0, 0, 0; -3, 1, 0, 0; 3, 0, 1, 0; 0, 0, 0, 1]

theorem twistBasisInvMatrix_mul_twistBasisMatrix (j : Kind) :
    twistBasisInvMatrix j * twistBasisMatrix j = 1 := by
  cases j <;> decide

theorem twistBasisMatrix_mul_twistBasisInvMatrix (j : Kind) :
    twistBasisMatrix j * twistBasisInvMatrix j = 1 := by
  cases j <;> decide

theorem twistBasisMatrix_det (j : Kind) :
    (twistBasisMatrix j).det = γ j.twist := by
  cases j <;> decide

theorem twistBasisMatrix_det_eq_one_or_neg_one (j : Kind) :
    (twistBasisMatrix j).det = 1 ∨ (twistBasisMatrix j).det = -1 := by
  cases j <;> decide

theorem twistBasisMatrix_det_isUnit (j : Kind) :
    IsUnit (twistBasisMatrix j).det := by
  rcases twistBasisMatrix_det_eq_one_or_neg_one j with h | h
  · rw [h]
    exact isUnit_one
  · rw [h]
    exact isUnit_neg_one

theorem twistBasisMatrix_first_column (j : Kind) :
    (fun i => twistBasisMatrix j i 0) = j.twist := by
  cases j <;> decide

theorem twistBasisMatrix_succ_column (j : Kind) (k : Fin 3) :
    (fun i => twistBasisMatrix j i k.succ) = Pi.single k.succ 1 := by
  cases j <;> fin_cases k <;> decide

/-- The block diagonal matrix `diag(1, fibreMatrix j)` in `Fin 4`
coordinates, with the first coordinate singled out. -/
def twistBlockMatrix (j : Kind) : LatticeMatrix :=
  !![1, 0, 0, 0;
     0, fibreMatrix j 0 0, fibreMatrix j 0 1, fibreMatrix j 0 2;
     0, fibreMatrix j 1 0, fibreMatrix j 1 1, fibreMatrix j 1 2;
     0, fibreMatrix j 2 0, fibreMatrix j 2 1, fibreMatrix j 2 2]

theorem twistBlockMatrix_zero_zero (j : Kind) : twistBlockMatrix j 0 0 = 1 := rfl

theorem twistBlockMatrix_zero_succ (j : Kind) (k : Fin 3) :
    twistBlockMatrix j 0 k.succ = 0 := by
  fin_cases k <;> rfl

theorem twistBlockMatrix_succ_zero (j : Kind) (i : Fin 3) :
    twistBlockMatrix j i.succ 0 = 0 := by
  fin_cases i <;> rfl

theorem twistBlockMatrix_succ_succ (j : Kind) (i k : Fin 3) :
    twistBlockMatrix j i.succ k.succ = fibreMatrix j i k := by
  fin_cases i <;> fin_cases k <;> rfl

/-- The source's actual elliptic matrix becomes the identity on the
twist coordinate and the restricted fibre matrix on the other three. -/
theorem twistBasisMatrix_conjugacy (j : Kind) :
    twistBasisInvMatrix j * j.matrix * twistBasisMatrix j = twistBlockMatrix j := by
  cases j <;> decide

theorem twistBlockMatrix_mulVec (j : Kind) (t : ℤ) (v : FibreLattice) :
    twistBlockMatrix j *ᵥ Fin.cons t v = Fin.cons t (fibreMatrix j *ᵥ v) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [twistBlockMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [Fin.cons_succ]
    fin_cases k <;>
      simp [twistBlockMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The actual integral linear equivalence given by the twist basis. -/
def twistBasisLinearEquiv (j : Kind) : Lattice ≃ₗ[ℤ] Lattice where
  __ := (twistBasisMatrix j).mulVecLin
  invFun := (twistBasisInvMatrix j).mulVecLin
  left_inv v := by
    change twistBasisInvMatrix j *ᵥ (twistBasisMatrix j *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, twistBasisInvMatrix_mul_twistBasisMatrix, Matrix.one_mulVec]
  right_inv v := by
    change twistBasisMatrix j *ᵥ (twistBasisInvMatrix j *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, twistBasisMatrix_mul_twistBasisInvMatrix, Matrix.one_mulVec]

@[simp] theorem twistBasisLinearEquiv_apply (j : Kind) (v : Lattice) :
    twistBasisLinearEquiv j v = twistBasisMatrix j *ᵥ v := rfl

@[simp] theorem twistBasisLinearEquiv_symm_apply (j : Kind) (v : Lattice) :
    (twistBasisLinearEquiv j).symm v = twistBasisInvMatrix j *ᵥ v := rfl

theorem twistBasisLinearEquiv_conjugacy (j : Kind) (v : Lattice) :
    (twistBasisLinearEquiv j).symm (j.matrix *ᵥ twistBasisLinearEquiv j v) =
      twistBlockMatrix j *ᵥ v := by
  change twistBasisInvMatrix j *ᵥ (j.matrix *ᵥ (twistBasisMatrix j *ᵥ v)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, twistBasisMatrix_conjugacy]

/-- Integral coordinates split into the twist direction and the fibre
lattice, using the verified change of basis. -/
def twistLatticeCoordinates (j : Kind) : Lattice ≃ₗ[ℤ] ℤ × FibreLattice :=
  (twistBasisLinearEquiv j).symm.trans
    (Fin.consLinearEquiv ℤ (fun _ : Fin 4 => ℤ)).symm

@[simp] theorem twistLatticeCoordinates_fst (j : Kind) (v : Lattice) :
    (twistLatticeCoordinates j v).1 = (twistBasisInvMatrix j *ᵥ v) 0 := rfl

@[simp] theorem twistLatticeCoordinates_snd (j : Kind) (v : Lattice) (i : Fin 3) :
    (twistLatticeCoordinates j v).2 i = (twistBasisInvMatrix j *ᵥ v) i.succ := rfl

@[simp] theorem twistLatticeCoordinates_symm_apply (j : Kind) (t : ℤ) (v : FibreLattice) :
    (twistLatticeCoordinates j).symm (t, v) = twistBasisMatrix j *ᵥ Fin.cons t v := rfl

end Wikipedia.HopfProblem.Elliptic.HigherHomology
