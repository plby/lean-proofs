import Wikipedia.HopfProblem.ConifoldStandardBoundaryAlgebra
import Wikipedia.HopfProblem.ConifoldStandardBoundaryParameter

/-!
# Literal level sets and inverse boundary maps

These subtypes are defined by the original determinant and the Frobenius norm.
The two inverse maps are restrictions of explicit real-linear ambient maps.
No atlas or manifold-recognition assertion is introduced here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

/-- The nonzero conifold level, expressed without a chosen small resolution. -/
abbrev ConifoldBoundary (r : ℝ) :=
  {M : MatrixSpace // M.det = 0 ∧ frobeniusSq M = r ^ 2}

/-- The corresponding literal level of the determinant-one smoothing. -/
abbrev SmoothingBoundary (r : ℝ) :=
  {M : MatrixSpace // M.det = 1 ∧ frobeniusSq M = r ^ 2 + (r ^ 2)⁻¹}

/-- The ambient matrix map `M ↦ M + r⁻² adj(M*)`. -/
def forward (r : ℝ) (M : MatrixSpace) : MatrixSpace :=
  deform (coefficient r) M

/-- The ambient inverse matrix map, normalized by `1 - r⁻⁴`. -/
def backward (r : ℝ) (M : MatrixSpace) : MatrixSpace :=
  (inverseScale r : ℂ) • deform (-coefficient r) M

theorem forward_formula (r : ℝ) (M : MatrixSpace) :
    forward r M = M + (((r ^ 2)⁻¹ : ℝ) : ℂ) • M.conjTranspose.adjugate := rfl

theorem backward_formula (r : ℝ) (M : MatrixSpace) :
    backward r M = (((1 - (r ^ 4)⁻¹)⁻¹ : ℝ) : ℂ) •
      (M - (((r ^ 2)⁻¹ : ℝ) : ℂ) • M.conjTranspose.adjugate) := by
  rw [backward, inverseScale, coefficient_sq_eq_inv_pow_four]
  simp only [deform, coefficient, adjointAdjugate, Complex.ofReal_neg, neg_smul,
    sub_eq_add_neg]

theorem backward_forward {r : ℝ} (hr : 1 < r) (M : MatrixSpace) :
    backward r (forward r M) = M := by
  rw [backward, forward, deform_deform_neg, smul_smul,
    ← Complex.ofReal_mul, inverseScale_mul_one_sub_sq hr,
    Complex.ofReal_one, one_smul]

theorem forward_backward {r : ℝ} (hr : 1 < r) (M : MatrixSpace) :
    forward r (backward r M) = M := by
  rw [forward, backward, deform_smul, deform_neg_deform, smul_smul,
    ← Complex.ofReal_mul, inverseScale_mul_one_sub_sq hr,
    Complex.ofReal_one, one_smul]

theorem det_forward {r : ℝ} (hr : 1 < r) {M : MatrixSpace}
    (hdet : M.det = 0) (hnorm : frobeniusSq M = r ^ 2) :
    (forward r M).det = 1 := by
  rw [forward, det_deform, hdet, hnorm]
  simp only [map_zero, mul_zero, zero_add, add_zero,
    ← Complex.ofReal_mul, coefficient_mul_sq hr, Complex.ofReal_one]

theorem frobeniusSq_forward {r : ℝ} (hr : 1 < r) {M : MatrixSpace}
    (hdet : M.det = 0) (hnorm : frobeniusSq M = r ^ 2) :
    frobeniusSq (forward r M) = r ^ 2 + (r ^ 2)⁻¹ := by
  rw [forward, frobeniusSq_deform, hdet, hnorm]
  simpa only [Complex.zero_re, mul_zero, add_zero] using forward_norm_scalar hr

theorem det_negative_deform {r : ℝ} (hr : 1 < r) {M : MatrixSpace}
    (hdet : M.det = 1) (hnorm : frobeniusSq M = r ^ 2 + (r ^ 2)⁻¹) :
    (deform (-coefficient r) M).det = 0 := by
  rw [det_deform, hdet, hnorm]
  calc
    (1 : ℂ) + ((-coefficient r : ℝ) : ℂ) * ((r ^ 2 + (r ^ 2)⁻¹ : ℝ) : ℂ) +
        ((-coefficient r : ℝ) : ℂ) ^ 2 * (starRingEnd ℂ) 1 =
        ((1 - coefficient r * (r ^ 2 + (r ^ 2)⁻¹) + coefficient r ^ 2 : ℝ) : ℂ) := by
      simp only [map_one, mul_one, Complex.ofReal_add, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_neg]
      ring
    _ = 0 := by rw [inverse_determinant_scalar hr, Complex.ofReal_zero]

theorem det_backward {r : ℝ} (hr : 1 < r) {M : MatrixSpace}
    (hdet : M.det = 1) (hnorm : frobeniusSq M = r ^ 2 + (r ^ 2)⁻¹) :
    (backward r M).det = 0 := by
  rw [backward, Matrix.det_smul, det_negative_deform hr hdet hnorm, mul_zero]

theorem frobeniusSq_backward {r : ℝ} (hr : 1 < r) {M : MatrixSpace}
    (hdet : M.det = 1) (hnorm : frobeniusSq M = r ^ 2 + (r ^ 2)⁻¹) :
    frobeniusSq (backward r M) = r ^ 2 := by
  rw [backward, frobeniusSq_smul, frobeniusSq_deform, hdet, hnorm]
  simpa only [neg_sq, Complex.one_re, mul_one, mul_neg, add_neg_cancel_right,
    sub_eq_add_neg] using inverse_norm_scalar hr

/-- The exact forward map between the two level subtypes. -/
def boundaryMap {r : ℝ} (hr : 1 < r) (M : ConifoldBoundary r) :
    SmoothingBoundary r :=
  ⟨forward r M.val, det_forward hr M.property.1 M.property.2,
    frobeniusSq_forward hr M.property.1 M.property.2⟩

/-- The exact inverse map between the two level subtypes. -/
def boundaryInverse {r : ℝ} (hr : 1 < r) (M : SmoothingBoundary r) :
    ConifoldBoundary r :=
  ⟨backward r M.val, det_backward hr M.property.1 M.property.2,
    frobeniusSq_backward hr M.property.1 M.property.2⟩

@[simp] theorem boundaryMap_val {r : ℝ} (hr : 1 < r) (M : ConifoldBoundary r) :
    (boundaryMap hr M).val = forward r M.val := rfl

@[simp] theorem boundaryInverse_val {r : ℝ} (hr : 1 < r) (M : SmoothingBoundary r) :
    (boundaryInverse hr M).val = backward r M.val := rfl

@[simp] theorem boundaryInverse_boundaryMap {r : ℝ} (hr : 1 < r)
    (M : ConifoldBoundary r) : boundaryInverse hr (boundaryMap hr M) = M := by
  apply Subtype.ext
  exact backward_forward hr M.val

@[simp] theorem boundaryMap_boundaryInverse {r : ℝ} (hr : 1 < r)
    (M : SmoothingBoundary r) : boundaryMap hr (boundaryInverse hr M) = M := by
  apply Subtype.ext
  exact forward_backward hr M.val

/-- The level equivalence has both original ambient formulas, not an abstract cardinality proof. -/
def boundaryEquiv {r : ℝ} (hr : 1 < r) : ConifoldBoundary r ≃ SmoothingBoundary r where
  toFun := boundaryMap hr
  invFun := boundaryInverse hr
  left_inv := boundaryInverse_boundaryMap hr
  right_inv := boundaryMap_boundaryInverse hr

end Wikipedia.HopfProblem.ConifoldStandardBoundary
