import Wikipedia.HopfProblem.ConifoldPolarRegionsLevels

/-!
# Explicit polar coordinates on the smoothing boundary

The original smoothing boundary is a Frobenius level of the determinant-one
matrix group.  Its positive-factor coordinate lies on the Euclidean sphere
of radius `(r - r⁻¹) / 2`.  The identification below preserves the original
matrix entries and both subspace topologies.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- The Euclidean base radius corresponding to the original smoothing level. -/
def boundaryRadius (r : ℝ) : ℝ := (r - r⁻¹) / 2

theorem boundaryRadius_pos {r : ℝ} (hr : 1 < r) : 0 < boundaryRadius r := by
  have hi : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  unfold boundaryRadius
  linarith

theorem boundaryRadius_level_eq {r : ℝ} (hr : 1 < r) :
    2 + 4 * (boundaryRadius r) ^ 2 = r ^ 2 + (r ^ 2)⁻¹ := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  rw [← inv_pow]
  unfold boundaryRadius
  nlinarith [mul_inv_cancel₀ hr0]

/-- Repackage the same matrix as a determinant-one matrix on its native level. -/
def smoothingLevelHomeomorph {r : ℝ} (hr : 1 < r) :
    SmoothingBoundary r ≃ₜ ↥(frobeniusLevel (boundaryRadius r)) where
  toFun M := ⟨⟨M.val, M.property.1⟩, by
    change frobeniusSq M.val = 2 + 4 * (boundaryRadius r) ^ 2
    rw [boundaryRadius_level_eq hr]
    exact M.property.2⟩
  invFun M := ⟨M.val.val, M.val.property, by
    rw [← boundaryRadius_level_eq hr]
    exact M.property⟩
  left_inv M := Subtype.ext rfl
  right_inv M := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := by
    have hg : Continuous (fun M : SpecialLinear => M.val) := continuous_subtype_val
    have hl : Continuous (fun M : ↥(frobeniusLevel (boundaryRadius r)) => M.val) :=
      continuous_subtype_val
    exact (hg.comp hl).subtype_mk _

@[simp] theorem smoothingLevelHomeomorph_val_val {r : ℝ} (hr : 1 < r)
    (M : SmoothingBoundary r) :
    (smoothingLevelHomeomorph hr M).val.val = M.val := rfl

@[simp] theorem smoothingLevelHomeomorph_symm_val {r : ℝ} (hr : 1 < r)
    (M : ↥(frobeniusLevel (boundaryRadius r))) :
    ((smoothingLevelHomeomorph hr).symm M).val = M.val.val := rfl

/-- The smoothing boundary is the indicated Euclidean two-sphere times the unit `S³`. -/
def smoothingBoundaryHomeomorph {r : ℝ} (hr : 1 < r) :
    SmoothingBoundary r ≃ₜ
      ↥(Metric.sphere (0 : Base) (boundaryRadius r)) × NormalSphere :=
  (smoothingLevelHomeomorph hr).trans
    (levelHomeomorph (boundaryRadius r) (boundaryRadius_pos hr).le)

@[simp] theorem smoothingBoundaryHomeomorph_fst_val {r : ℝ} (hr : 1 < r)
    (M : SmoothingBoundary r) :
    (smoothingBoundaryHomeomorph hr M).1.val = baseCoordinates (positivePart M.val) := rfl

@[simp] theorem smoothingBoundaryHomeomorph_snd_val {r : ℝ} (hr : 1 < r)
    (M : SmoothingBoundary r) :
    (smoothingBoundaryHomeomorph hr M).2.val = normalCoordinates (unitaryPart M.val) := rfl

@[simp] theorem smoothingBoundaryHomeomorph_symm_val {r : ℝ} (hr : 1 < r)
    (q : ↥(Metric.sphere (0 : Base) (boundaryRadius r)) × NormalSphere) :
    ((smoothingBoundaryHomeomorph hr).symm q).val =
      positiveMatrix q.1.val * unitaryMatrix q.2.val := rfl

theorem smoothingLevelHomeomorph_circle {r : ℝ} (hr : 1 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (M : SmoothingBoundary r) :
    smoothingLevelHomeomorph hr (smoothingCircle u hu M) =
      levelCircleAction (boundaryRadius r) u hu (smoothingLevelHomeomorph hr M) := rfl

/-- The original matrix circle action fixes the base and rotates the original normal sphere. -/
theorem smoothingBoundaryHomeomorph_circle {r : ℝ} (hr : 1 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (M : SmoothingBoundary r) :
    smoothingBoundaryHomeomorph hr (smoothingCircle u hu M) =
      ((smoothingBoundaryHomeomorph hr M).1,
        sphereRotation u hu (smoothingBoundaryHomeomorph hr M).2) := by
  change levelHomeomorph (boundaryRadius r) (boundaryRadius_pos hr).le
    (smoothingLevelHomeomorph hr (smoothingCircle u hu M)) = _
  rw [smoothingLevelHomeomorph_circle]
  exact levelHomeomorph_circleAction (boundaryRadius r) (boundaryRadius_pos hr).le
    u hu (smoothingLevelHomeomorph hr M)

end Wikipedia.HopfProblem.ConifoldPolar
