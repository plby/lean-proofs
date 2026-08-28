import Wikipedia.HopfProblem.SmoothCircleApproximation

/-!
# The nonvanishing segment for a close approximation of a unit phase

The actual real affine segment is jointly continuous and has the literal
endpoint maps. A half-unit bound from a unit-valued starting map keeps
the whole segment at norm at least one half, so radial normalization is
defined throughout the homotopy.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SmoothCirclePhaseHomotopy

variable {M : Type*} (f g : M → ℂ)

/-- The actual real affine segment in the original complex plane. -/
def segment (t : unitInterval) (x : M) : ℂ :=
  (1 - (t : ℝ)) • f x + (t : ℝ) • g x

@[simp] theorem segment_zero (x : M) : segment f g 0 x = f x := by
  simp [segment]

@[simp] theorem segment_one (x : M) : segment f g 1 x = g x := by
  simp [segment]

/-- At a point where the two maps agree the whole segment is stationary. -/
theorem segment_of_eq (t : unitInterval) (x : M) (h : g x = f x) :
    segment f g t x = f x := by
  simp [segment, h, sub_smul]

/-- The actual displacement is the real parameter times the original difference. -/
theorem segment_sub_left (t : unitInterval) (x : M) :
    segment f g t x - f x = (t : ℝ) • (g x - f x) := by
  simp only [segment, sub_smul, one_smul, smul_sub]
  abel

/-- Joint continuity needs only the original topology on the source. -/
theorem continuous_segment [TopologicalSpace M] (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : unitInterval × M => segment f g p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (hf.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (hg.comp continuous_snd))

/-- Every point of the segment retains the given half-unit displacement bound. -/
theorem segment_dist_left_le_half
    (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) (t : unitInterval) (x : M) :
    dist (segment f g t x) (f x) ≤ (1 / 2 : ℝ) := by
  rw [dist_eq_norm, segment_sub_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg t.property.1]
  calc
    (t : ℝ) * ‖g x - f x‖ ≤ 1 * ‖g x - f x‖ :=
      mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
    _ = dist (g x) (f x) := by rw [one_mul, dist_eq_norm]
    _ ≤ (1 / 2 : ℝ) := hclose x

/-- A close segment starting at a unit phase stays uniformly away from zero. -/
theorem segment_norm_lower (hunit : ∀ x, ‖f x‖ = 1)
    (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) (t : unitInterval) (x : M) :
    (1 / 2 : ℝ) ≤ ‖segment f g t x‖ := by
  have hdist := segment_dist_left_le_half f g hclose t x
  have hnorm := norm_sub_norm_le (f x) (segment f g t x)
  rw [hunit x, norm_sub_rev] at hnorm
  rw [dist_eq_norm] at hdist
  linarith

/-- The literal segment never vanishes under the same quantitative hypotheses. -/
theorem segment_ne_zero (hunit : ∀ x, ‖f x‖ = 1)
    (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) (t : unitInterval) (x : M) :
    segment f g t x ≠ 0 := by
  intro hzero
  have h := segment_norm_lower f g hunit hclose t x
  rw [hzero, norm_zero] at h
  norm_num at h

end Wikipedia.HopfProblem.SmoothCirclePhaseHomotopy
