import Wikipedia.HopfProblem.ConifoldStandardBoundaryLevels
import Wikipedia.HopfProblem.ConifoldStandardBoundaryCircle
import Wikipedia.HopfProblem.ConifoldStandardBoundaryRegularity

/-!
# An explicit circle-equivariant standard conifold boundary homeomorphism

For `1 < r`, the map `M ↦ M + r⁻² adj(M*)` identifies the literal subspace
`{det M = 0, |M|² = r²}` with `{det M = 1, |M|² = r² + r⁻²}`.  Its inverse
is `(N - r⁻² adj(N*)) / (1 - r⁻⁴)`.  Both maps are smooth on the ambient
real vector space, and they commute with right multiplication by
`diag(u⁻¹, u)` for every unit complex number.

The result uses the usual subspace topologies.  It does not equip either
level with an arbitrarily transported smooth structure, identify a global
threefold complement with this model, or assert a sphere recognition theorem.
-/

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

theorem forward_continuous (r : ℝ) : Continuous (forward r) :=
  deform_continuous (coefficient r)

theorem backward_continuous (r : ℝ) : Continuous (backward r) :=
  (continuous_const : Continuous (fun _ : MatrixSpace => (inverseScale r : ℂ))).smul
    (deform_continuous (-coefficient r))

/-- The forward formula is smooth as a map of the ambient real vector space. -/
theorem forward_contDiff (r : ℝ) {n : ℕ∞ω} : ContDiff ℝ n (forward r) :=
  deform_contDiff (coefficient r)

/-- The inverse formula is also smooth on the whole ambient real vector space. -/
theorem backward_contDiff (r : ℝ) {n : ℕ∞ω} : ContDiff ℝ n (backward r) :=
  (contDiff_const : ContDiff ℝ n (fun _ : MatrixSpace => (inverseScale r : ℂ))).smul
    (deform_contDiff (-coefficient r))

theorem boundaryMap_continuous {r : ℝ} (hr : 1 < r) : Continuous (boundaryMap hr) :=
  ((forward_continuous r).comp continuous_subtype_val).subtype_mk _

theorem boundaryInverse_continuous {r : ℝ} (hr : 1 < r) :
    Continuous (boundaryInverse hr) :=
  ((backward_continuous r).comp continuous_subtype_val).subtype_mk _

/-- The standard conifold and smoothing boundaries with their actual subspace topologies. -/
def boundaryHomeomorph {r : ℝ} (hr : 1 < r) :
    ConifoldBoundary r ≃ₜ SmoothingBoundary r where
  toEquiv := boundaryEquiv hr
  continuous_toFun := boundaryMap_continuous hr
  continuous_invFun := boundaryInverse_continuous hr

@[simp] theorem boundaryHomeomorph_apply_val {r : ℝ} (hr : 1 < r)
    (M : ConifoldBoundary r) : (boundaryHomeomorph hr M).val = forward r M.val := rfl

@[simp] theorem boundaryHomeomorph_symm_apply_val {r : ℝ} (hr : 1 < r)
    (M : SmoothingBoundary r) :
    ((boundaryHomeomorph hr).symm M).val = backward r M.val := rfl

/-- The circle acts on the conifold boundary by its original right matrix multiplication. -/
def conifoldCircle {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1)
    (M : ConifoldBoundary r) : ConifoldBoundary r :=
  ⟨rightCircle u M.val, (det_rightCircle u hu M.val).trans M.property.1,
    (frobeniusSq_rightCircle u hu M.val).trans M.property.2⟩

/-- The same literal matrix action restricts to the smoothing boundary. -/
def smoothingCircle {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1)
    (M : SmoothingBoundary r) : SmoothingBoundary r :=
  ⟨rightCircle u M.val, (det_rightCircle u hu M.val).trans M.property.1,
    (frobeniusSq_rightCircle u hu M.val).trans M.property.2⟩

@[simp] theorem conifoldCircle_val {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1)
    (M : ConifoldBoundary r) : (conifoldCircle u hu M).val = rightCircle u M.val := rfl

@[simp] theorem smoothingCircle_val {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1)
    (M : SmoothingBoundary r) : (smoothingCircle u hu M).val = rightCircle u M.val := rfl

theorem forward_rightCircle (r : ℝ) (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    forward r (rightCircle u M) = rightCircle u (forward r M) :=
  deform_rightCircle (coefficient r) u hu M

theorem backward_rightCircle (r : ℝ) (u : ℂ) (hu : ‖u‖ = 1) (M : MatrixSpace) :
    backward r (rightCircle u M) = rightCircle u (backward r M) := by
  rw [backward, deform_rightCircle _ u hu, smul_rightCircle]
  rfl

/-- The homeomorphism preserves the marked, opposite-weight circle action. -/
theorem boundaryHomeomorph_circle {r : ℝ} (hr : 1 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (M : ConifoldBoundary r) :
    boundaryHomeomorph hr (conifoldCircle u hu M) =
      smoothingCircle u hu (boundaryHomeomorph hr M) := by
  apply Subtype.ext
  exact forward_rightCircle r u hu M.val

/-- The displayed inverse preserves the same circle action. -/
theorem boundaryHomeomorph_symm_circle {r : ℝ} (hr : 1 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (M : SmoothingBoundary r) :
    (boundaryHomeomorph hr).symm (smoothingCircle u hu M) =
      conifoldCircle u hu ((boundaryHomeomorph hr).symm M) := by
  apply Subtype.ext
  exact backward_rightCircle r u hu M.val

theorem conifoldCircle_continuous {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1) :
    Continuous (conifoldCircle (r := r) u hu) :=
  ((continuous_rightCircle u).comp continuous_subtype_val).subtype_mk _

theorem smoothingCircle_continuous {r : ℝ} (u : ℂ) (hu : ‖u‖ = 1) :
    Continuous (smoothingCircle (r := r) u hu) :=
  ((continuous_rightCircle u).comp continuous_subtype_val).subtype_mk _

end Wikipedia.HopfProblem.ConifoldStandardBoundary
