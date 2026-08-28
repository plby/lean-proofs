import Wikipedia.HopfProblem.ConifoldStandardBoundary

/-!
# Changing the radius of the standard conifold boundary

The conifold link may arise at a small positive tubular radius.  A literal
positive homothety changes this radius to any other positive radius and
preserves the original circle action.  In particular, the hypothesis `1 < r`
in the smoothing map does not restrict which positive conifold link is used.
-/

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

/-- Ambient real homothety from radius `r` to radius `s`. -/
def rescaleMatrix (r s : ℝ) (M : MatrixSpace) : MatrixSpace :=
  ((s / r : ℝ) : ℂ) • M

theorem rescaleMatrix_continuous (r s : ℝ) : Continuous (rescaleMatrix r s) :=
  (continuous_const : Continuous (fun _ : MatrixSpace => ((s / r : ℝ) : ℂ))).smul
    continuous_id

theorem rescaleMatrix_contDiff (r s : ℝ) {n : ℕ∞ω} :
    ContDiff ℝ n (rescaleMatrix r s) :=
  (contDiff_const : ContDiff ℝ n (fun _ : MatrixSpace => ((s / r : ℝ) : ℂ))).smul
    contDiff_id

theorem det_rescaleMatrix (r s : ℝ) {M : MatrixSpace} (hM : M.det = 0) :
    (rescaleMatrix r s M).det = 0 := by
  rw [rescaleMatrix, Matrix.det_smul, hM, mul_zero]

theorem frobeniusSq_rescaleMatrix {r : ℝ} (hr : r ≠ 0) (s : ℝ)
    {M : MatrixSpace} (hM : frobeniusSq M = r ^ 2) :
    frobeniusSq (rescaleMatrix r s M) = s ^ 2 := by
  rw [rescaleMatrix, frobeniusSq_smul, hM]
  field_simp

theorem rescaleMatrix_rescaleMatrix {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (M : MatrixSpace) : rescaleMatrix s r (rescaleMatrix r s M) = M := by
  rw [rescaleMatrix, rescaleMatrix, smul_smul, ← Complex.ofReal_mul]
  have h : r / s * (s / r) = 1 := by field_simp
  rw [h, Complex.ofReal_one, one_smul]

/-- The homothety on the literal determinant-zero boundary subtype. -/
def rescaleBoundary {r : ℝ} (hr : r ≠ 0) (s : ℝ)
    (M : ConifoldBoundary r) : ConifoldBoundary s :=
  ⟨rescaleMatrix r s M.val, det_rescaleMatrix r s M.property.1,
    frobeniusSq_rescaleMatrix hr s M.property.2⟩

@[simp] theorem rescaleBoundary_val {r : ℝ} (hr : r ≠ 0) (s : ℝ)
    (M : ConifoldBoundary r) : (rescaleBoundary hr s M).val = rescaleMatrix r s M.val := rfl

theorem rescaleBoundary_continuous {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    Continuous (rescaleBoundary hr s) :=
  ((rescaleMatrix_continuous r s).comp continuous_subtype_val).subtype_mk _

/-- Original subspace topologies are preserved by the two reciprocal homotheties. -/
def rescaleHomeomorph {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    ConifoldBoundary r ≃ₜ ConifoldBoundary s where
  toFun := rescaleBoundary hr s
  invFun := rescaleBoundary hs r
  left_inv M := Subtype.ext (rescaleMatrix_rescaleMatrix hr hs M.val)
  right_inv M := Subtype.ext (rescaleMatrix_rescaleMatrix hs hr M.val)
  continuous_toFun := rescaleBoundary_continuous hr s
  continuous_invFun := rescaleBoundary_continuous hs r

theorem rescaleMatrix_rightCircle (r s : ℝ) (u : ℂ) (M : MatrixSpace) :
    rescaleMatrix r s (rightCircle u M) = rightCircle u (rescaleMatrix r s M) :=
  smul_rightCircle (s / r) u M

theorem rescaleHomeomorph_circle {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (u : ℂ) (hu : ‖u‖ = 1) (M : ConifoldBoundary r) :
    rescaleHomeomorph hr hs (conifoldCircle u hu M) =
      conifoldCircle u hu (rescaleHomeomorph hr hs M) := by
  apply Subtype.ext
  exact rescaleMatrix_rightCircle r s u M.val

/-- Every positive conifold radius maps to one fixed smoothing boundary. -/
def normalizedBoundaryHomeomorph {r : ℝ} (hr : 0 < r) :
    ConifoldBoundary r ≃ₜ SmoothingBoundary 2 :=
  (rescaleHomeomorph (ne_of_gt hr) (by norm_num : (2 : ℝ) ≠ 0)).trans
    (boundaryHomeomorph (by norm_num : (1 : ℝ) < 2))

@[simp] theorem normalizedBoundaryHomeomorph_apply_val {r : ℝ} (hr : 0 < r)
    (M : ConifoldBoundary r) :
    (normalizedBoundaryHomeomorph hr M).val = forward 2 (rescaleMatrix r 2 M.val) := rfl

theorem normalizedBoundaryHomeomorph_circle {r : ℝ} (hr : 0 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (M : ConifoldBoundary r) :
    normalizedBoundaryHomeomorph hr (conifoldCircle u hu M) =
      smoothingCircle u hu (normalizedBoundaryHomeomorph hr M) := by
  apply Subtype.ext
  exact (congrArg (forward 2) (rescaleMatrix_rightCircle r 2 u M.val)).trans
    (forward_rightCircle 2 u hu (rescaleMatrix r 2 M.val))

theorem conifoldBoundary_ne_zero {r : ℝ} (hr : r ≠ 0) (M : ConifoldBoundary r) :
    M.val ≠ 0 := by
  intro hM
  have hzero : frobeniusSq M.val = 0 := by simp [hM, frobeniusSq]
  exact pow_ne_zero 2 hr (M.property.2.symm.trans hzero)

end Wikipedia.HopfProblem.ConifoldStandardBoundary
