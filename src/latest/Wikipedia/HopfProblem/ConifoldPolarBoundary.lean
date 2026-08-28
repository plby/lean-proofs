import Wikipedia.HopfProblem.ConifoldPolarMatrixAlgebra
import Wikipedia.HopfProblem.ConifoldPolarBoundaryCoordinates
import Wikipedia.HopfProblem.ConifoldStandardBoundaryFrame

/-!
# The explicit polar formula on the marked conifold boundary

On the original rank-one radius level, the polar unitary factor is the
normalized sum of the matrix and its adjoint adjugate.  In the fixed frame
`(v, jVector v)`, it is exactly the existing product of `unitaryFrame v` and
`rowFrame r α β`; the Hermitian factor has the corresponding marked radial
diagonal.  All assertions concern literal matrices and their original entries.
-/

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

theorem deform_one_forward (r : ℝ) (M : MatrixSpace) :
    deform 1 (forward r M) = ((1 + coefficient r : ℝ) : ℂ) • deform 1 M := by
  rw [forward, deform, adjointAdjugate_deform]
  ext i j
  simp only [deform, Matrix.add_apply, Matrix.smul_apply, Complex.ofReal_one,
    smul_eq_mul, Complex.ofReal_add]
  ring

theorem denominator_forward {r : ℝ} (hr : 1 < r) (M : MatrixSpace)
    (hdet : M.det = 0) (hnorm : frobeniusSq M = r ^ 2) :
    denominator (forward r M) = r + r⁻¹ := by
  have hpos : 0 < r + r⁻¹ := add_pos (r_pos hr) (inv_pos.mpr (r_pos hr))
  have hsq : (r + r⁻¹) ^ 2 = r ^ 2 + (r ^ 2)⁻¹ + 2 := by
    field_simp [r_ne_zero hr]
    ring
  have hd := denominator_sq (forward r M)
  rw [frobeniusSq_forward hr hdet hnorm] at hd
  have hdpos := denominator_pos (forward r M)
  nlinarith

private theorem boundary_unitary_scalar {r : ℝ} (hr : 1 < r) :
    (r + r⁻¹)⁻¹ * (1 + coefficient r) = r⁻¹ := by
  have hsum : r + r⁻¹ ≠ 0 :=
    ne_of_gt (add_pos (r_pos hr) (inv_pos.mpr (r_pos hr)))
  unfold coefficient
  field_simp [r_ne_zero hr, hsum]

/-- The original boundary matrix has the explicit normalized quaternionic factor. -/
theorem unitaryPart_forward {r : ℝ} (hr : 1 < r) (M : MatrixSpace)
    (hdet : M.det = 0) (hnorm : frobeniusSq M = r ^ 2) :
    unitaryPart (forward r M) = ((r⁻¹ : ℝ) : ℂ) • deform 1 M := by
  rw [unitaryPart, denominator_forward hr M hdet hnorm,
    deform_one_forward, smul_smul, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, boundary_unitary_scalar hr]

theorem scaled_deform_one_rankOneMatrix (r : ℝ) (v : Fin 2 → ℂ) (α β : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) • deform 1 (rankOneMatrix v α β) =
      unitaryFrame v * rowFrame r α β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deform, rankOneMatrix, adjointAdjugate_entries, unitaryFrame, rowFrame,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_inv, div_eq_mul_inv] <;> ring

/-- The exact unitary factor in the existing marked normal frame. -/
theorem unitaryPart_forward_rankOneMatrix {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    unitaryPart (forward r (rankOneMatrix v α β)) =
      unitaryFrame v * rowFrame r α β := by
  have hnorm : frobeniusSq (rankOneMatrix v α β) = r ^ 2 := by
    rw [frobeniusSq_rankOneMatrix, hv, hαβ, one_mul]
  exact (unitaryPart_forward hr _ (det_rankOneMatrix v α β) hnorm).trans
    (scaled_deform_one_rankOneMatrix r v α β)

/-- The Hermitian factor has the original radial diagonal in the frame of `v`. -/
theorem positivePart_forward_rankOneMatrix {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    positivePart (forward r (rankOneMatrix v α β)) =
      unitaryFrame v * radialDiagonal r * (unitaryFrame v).conjTranspose := by
  rw [positivePart, unitaryPart_forward_rankOneMatrix hr v hv α β hαβ,
    forward_rankOneMatrix r (r_ne_zero hr), Matrix.conjTranspose_mul]
  calc
    (unitaryFrame v * radialDiagonal r * rowFrame r α β) *
        ((rowFrame r α β).conjTranspose * (unitaryFrame v).conjTranspose) =
        ((unitaryFrame v * radialDiagonal r) *
          (rowFrame r α β * (rowFrame r α β).conjTranspose)) *
            (unitaryFrame v).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [rowFrame_mul_conjTranspose r (r_ne_zero hr) α β hαβ, mul_one]

/-- The polar normal column retains the specified `jVector` sign and row conjugation. -/
theorem unitaryPart_forward_rankOneMatrix_secondColumn {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) (i : Fin 2) :
    unitaryPart (forward r (rankOneMatrix v α β)) i 1 =
      (v i * β + jVector v i * conj α) / (r : ℂ) := by
  rw [unitaryPart_forward_rankOneMatrix hr v hv α β hαβ]
  exact unitaryFrame_mul_rowFrame_secondColumn r v α β i

/-- The four real normal coordinates of the polar unitary factor in the original marking. -/
theorem normalCoordinates_unitaryPart_forward_rankOneMatrix {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    normalCoordinates (unitaryPart (forward r (rankOneMatrix v α β))) =
      (EuclideanSpace.equiv (Fin 4) ℝ).symm
        ![((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).re,
          ((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).im,
          ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).re,
          ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).im] := by
  rw [unitaryPart_forward_rankOneMatrix hr v hv α β hαβ]
  exact normalCoordinates_unitaryFrame_mul_rowFrame r v α β

end Wikipedia.HopfProblem.ConifoldPolar
