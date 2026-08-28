import Wikipedia.HopfProblem.ConifoldStandardBoundary

/-!
# Concrete marked frames for the standard conifold boundary

The rank-one matrix with columns `v α` and `v β` has an explicit factorization
after applying the standard boundary map.  The second column of the unitary
factor is computed in the original normal frame `(v, jVector v)`.
No global polar-coordinate or complement-identification assertion is used.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

/-- The conjugate perpendicular vector with the specified normal-frame sign. -/
def jVector (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![-conj (v 1), conj (v 0)]

/-- The matrix whose columns are the original vector and its marked perpendicular. -/
def unitaryFrame (v : Fin 2 → ℂ) : MatrixSpace :=
  !![v 0, -conj (v 1); v 1, conj (v 0)]

/-- A rank-one matrix with its two columns in the line spanned by `v`. -/
def rankOneMatrix (v : Fin 2 → ℂ) (α β : ℂ) : MatrixSpace :=
  !![v 0 * α, v 0 * β; v 1 * α, v 1 * β]

/-- The normalized row coordinates, completed using the fixed conjugation signs. -/
def rowFrame (r : ℝ) (α β : ℂ) : MatrixSpace :=
  !![α / (r : ℂ), β / (r : ℂ); -conj β / (r : ℂ), conj α / (r : ℂ)]

/-- The positive radial diagonal when `r > 0`. -/
def radialDiagonal (r : ℝ) : MatrixSpace := Matrix.diagonal ![(r : ℂ), (r : ℂ)⁻¹]

@[simp] theorem unitaryFrame_firstColumn (v : Fin 2 → ℂ) (i : Fin 2) :
    unitaryFrame v i 0 = v i := by
  fin_cases i <;> rfl

@[simp] theorem unitaryFrame_secondColumn (v : Fin 2 → ℂ) (i : Fin 2) :
    unitaryFrame v i 1 = jVector v i := by
  fin_cases i <;> rfl

theorem det_rankOneMatrix (v : Fin 2 → ℂ) (α β : ℂ) :
    (rankOneMatrix v α β).det = 0 := by
  simp [rankOneMatrix, Matrix.det_fin_two]
  ring

theorem frobeniusSq_rankOneMatrix (v : Fin 2 → ℂ) (α β : ℂ) :
    frobeniusSq (rankOneMatrix v α β) =
      (Complex.normSq (v 0) + Complex.normSq (v 1)) *
        (Complex.normSq α + Complex.normSq β) := by
  simp [frobeniusSq_entries, rankOneMatrix, Complex.normSq_mul]
  ring

theorem det_unitaryFrame (v : Fin 2 → ℂ)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1) :
    (unitaryFrame v).det = 1 := by
  simp [unitaryFrame, Matrix.det_fin_two, Complex.mul_conj,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add, hv]

theorem unitaryFrame_conjTranspose_mul (v : Fin 2 → ℂ)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1) :
    (unitaryFrame v).conjTranspose * unitaryFrame v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFrame, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_add, hv, add_comm] <;> ring

theorem unitaryFrame_mul_conjTranspose (v : Fin 2 → ℂ)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1) :
    unitaryFrame v * (unitaryFrame v).conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFrame, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_conj,
      ← Complex.ofReal_add, hv, add_comm] <;> ring

theorem rowFrame_eq_unitaryFrame (r : ℝ) (α β : ℂ) :
    rowFrame r α β = unitaryFrame ![α / (r : ℂ), -conj β / (r : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowFrame, unitaryFrame, neg_div]

private theorem rowFrame_unit_norm (r : ℝ) (hr : r ≠ 0) (α β : ℂ)
    (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    Complex.normSq (![α / (r : ℂ), -conj β / (r : ℂ)] 0) +
      Complex.normSq (![α / (r : ℂ), -conj β / (r : ℂ)] 1) = 1 := by
  simp [← add_div, hαβ, pow_two, hr]

theorem det_rowFrame (r : ℝ) (hr : r ≠ 0) (α β : ℂ)
    (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (rowFrame r α β).det = 1 := by
  rw [rowFrame_eq_unitaryFrame]
  exact det_unitaryFrame _ (rowFrame_unit_norm r hr α β hαβ)

theorem rowFrame_conjTranspose_mul (r : ℝ) (hr : r ≠ 0) (α β : ℂ)
    (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (rowFrame r α β).conjTranspose * rowFrame r α β = 1 := by
  rw [rowFrame_eq_unitaryFrame]
  exact unitaryFrame_conjTranspose_mul _ (rowFrame_unit_norm r hr α β hαβ)

theorem rowFrame_mul_conjTranspose (r : ℝ) (hr : r ≠ 0) (α β : ℂ)
    (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    rowFrame r α β * (rowFrame r α β).conjTranspose = 1 := by
  rw [rowFrame_eq_unitaryFrame]
  exact unitaryFrame_mul_conjTranspose _ (rowFrame_unit_norm r hr α β hαβ)

/-- Exact radial factorization of the explicit standard boundary map. -/
theorem forward_rankOneMatrix (r : ℝ) (hr : r ≠ 0) (v : Fin 2 → ℂ) (α β : ℂ) :
    forward r (rankOneMatrix v α β) =
      unitaryFrame v * radialDiagonal r * rowFrame r α β := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [forward, deform, coefficient, rankOneMatrix, adjointAdjugate_entries,
      unitaryFrame, rowFrame, radialDiagonal, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] <;>
    field_simp [hrC]

/-- The unitary factor's second column is expressed in the original marked frame. -/
theorem unitaryFrame_mul_rowFrame_secondColumn (r : ℝ) (v : Fin 2 → ℂ)
    (α β : ℂ) (i : Fin 2) :
    (unitaryFrame v * rowFrame r α β) i 1 =
      (v i * β + jVector v i * conj α) / (r : ℂ) := by
  fin_cases i <;>
    simp [unitaryFrame, rowFrame, jVector, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The same factorization grouped as a conjugated radial factor times the marked frame. -/
theorem forward_rankOneMatrix_leftFactor (r : ℝ) (hr : r ≠ 0) (v : Fin 2 → ℂ)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1) (α β : ℂ) :
    forward r (rankOneMatrix v α β) =
      (unitaryFrame v * radialDiagonal r * (unitaryFrame v).conjTranspose) *
        (unitaryFrame v * rowFrame r α β) := by
  rw [forward_rankOneMatrix r hr v α β]
  calc
    unitaryFrame v * radialDiagonal r * rowFrame r α β =
        (unitaryFrame v * radialDiagonal r) *
          (((unitaryFrame v).conjTranspose * unitaryFrame v) * rowFrame r α β) := by
      rw [unitaryFrame_conjTranspose_mul v hv, one_mul]
    _ = _ := by simp only [mul_assoc]

end Wikipedia.HopfProblem.ConifoldStandardBoundary
