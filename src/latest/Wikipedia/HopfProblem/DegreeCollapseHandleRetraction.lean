import Wikipedia.HopfProblem.DegreeCollapseHandleRetractionBasic

/-!
# The continuous retraction of a handle to its attaching face and core

The normalized positive-coordinate formula is continuous even when that
coordinate vanishes, because its output norm is bounded by the input norm.
The attaching face and the entire core disk are fixed pointwise.
-/

noncomputable section

open Set Metric Filter Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.Handle

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ N] [NormedSpace ℝ P] in
theorem continuous_denominator : Continuous (denominator (N := N) (P := P)) := by
  unfold denominator
  fun_prop

omit [NormedSpace ℝ P] in
theorem continuous_negative : Continuous (negative (N := N) (P := P)) :=
  (continuous_denominator.inv₀ (fun z => (denominator_pos z).ne')).smul
    (continuous_subtype_val.comp continuous_fst)

omit [NormedSpace ℝ N] in
theorem continuous_positive : Continuous (positive (N := N) (P := P)) := by
  have hv : Continuous (fun z : Space (N := N) (P := P) => (z.2 : P)) :=
    continuous_subtype_val.comp continuous_snd
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : (z.2 : P) = 0
  · change Tendsto positive (𝓝 z) (𝓝 (positive z))
    rw [positive_eq_zero_of_snd_eq_zero z hz]
    apply squeeze_zero_norm norm_positive_le
    simpa only [hz, norm_zero] using hv.norm.continuousAt.tendsto (x := z)
  · have hn : Continuous (fun w : Space (N := N) (P := P) =>
        2 * denominator w + ‖(w.2 : P)‖ - 2) :=
      ((continuous_const.mul continuous_denominator).add hv.norm).sub continuous_const
    have hd : Continuous (fun w : Space (N := N) (P := P) =>
        ‖(w.2 : P)‖ * denominator w) := hv.norm.mul continuous_denominator
    exact (hn.continuousAt.div hd.continuousAt
      (mul_ne_zero (norm_ne_zero_iff.mpr hz) (denominator_pos z).ne')).smul hv.continuousAt

/-- The actual closed-disk product map, not a quotient of its homology. -/
def retraction : C(Space (N := N) (P := P), Space (N := N) (P := P)) where
  toFun z := (⟨negative z, mem_closedBall_zero_iff.mpr (norm_negative_le_one z)⟩,
    ⟨positive z, mem_closedBall_zero_iff.mpr
      ((norm_positive_le z).trans (mem_closedBall_zero_iff.mp z.2.property))⟩)
  continuous_toFun := (continuous_negative.subtype_mk _).prodMk
    (continuous_positive.subtype_mk _)

/-- The attaching face together with the negative core disk. -/
def faceCore : Set (Space (N := N) (P := P)) := {z | ‖(z.1 : N)‖ = 1 ∨ (z.2 : P) = 0}

theorem retraction_mem_faceCore (z : Space (N := N) (P := P)) :
    retraction z ∈ faceCore := by
  by_cases hz : 1 - ‖(z.2 : P)‖ / 2 ≤ ‖(z.1 : N)‖
  · left
    change ‖negative z‖ = 1
    have hd : denominator z = ‖(z.1 : N)‖ := max_eq_left hz
    rw [negative, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (denominator_pos z).le)]
    rw [← hd, inv_mul_cancel₀ (denominator_pos z).ne']
  · right
    change positive z = 0
    have hd : denominator z = 1 - ‖(z.2 : P)‖ / 2 := max_eq_right (le_of_not_ge hz)
    have hn : 2 * denominator z + ‖(z.2 : P)‖ - 2 = 0 := by rw [hd]; ring
    simp only [positive, positiveMultiplier, hn, zero_div, zero_smul]

theorem retraction_eq_self (z : Space (N := N) (P := P)) (hz : z ∈ faceCore) :
    retraction z = z := by
  have hd : denominator z = 1 := by
    rcases hz with hu | hv
    · unfold denominator
      rw [hu]
      apply max_eq_left
      linarith [norm_nonneg (z.2 : P)]
    · exact denominator_eq_one_of_snd_eq_zero z hv
  apply Prod.ext
  · apply Subtype.ext
    change negative z = (z.1 : N)
    simp only [negative, hd, inv_one, one_smul]
  · apply Subtype.ext
    change positive z = (z.2 : P)
    by_cases hv : (z.2 : P) = 0
    · simp only [positive, hv, smul_zero]
    · have hm : positiveMultiplier z = 1 := by
        unfold positiveMultiplier
        rw [hd]
        field_simp
        ring
      rw [positive, hm, one_smul]

end Wikipedia.HopfProblem.DegreeCollapse.Handle
