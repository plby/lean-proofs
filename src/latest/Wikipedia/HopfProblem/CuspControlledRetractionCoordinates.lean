import Wikipedia.HopfProblem.CuspRetractionDisplacement
import Wikipedia.HopfProblem.CuspRetractionPosition
import Wikipedia.HopfProblem.CuspPositiveRetractionPhases
import Wikipedia.HopfProblem.CuspHoneycombTilingBasic

/-!
# Normalized coordinates for the controlled cusp collapse

On each nonzero small time fibre, inversion of the actual positive-twist
displacement turns the deck action into the ordinary honeycomb lattice
translation.  These coordinates are continuous on the punctured tube.
Their total extension by zero on the central fibre is only used for
bounds; no continuity or translation covariance is asserted there.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace ToricFan CuspPositive

local notation "Plane" => Fin 2 → ℝ

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The source's normalized position `ℓ_|t| y`, using the genuine
inverse of the positive logarithmic displacement. -/
def normalizedPosition (x : Space) : Plane :=
  realCuspVector
    (inverseDisplacement (positiveTwist C₀) (time x) (position x))

/-- The height-indexed linear normalization, with no choice of inverse. -/
def normalization (h : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  realCuspVector.comp (inverseDisplacement (positiveTwist C₀) (h : ℂ))

theorem inverseDisplacement_positiveTwist_norm (t : ℂ) :
    inverseDisplacement (positiveTwist C₀) (‖t‖ : ℂ) =
      inverseDisplacement (positiveTwist C₀) t := by
  unfold inverseDisplacement
  congr 1
  simp only [displacementMatrix, driftMatrix_positiveTwist,
    Complex.norm_of_nonneg (norm_nonneg t)]

theorem normalizedPosition_eq_normalization (x : Space) :
    normalizedPosition C₀ x = normalization C₀ ‖time x‖ (position x) := by
  simp only [normalizedPosition, normalization, LinearMap.comp_apply,
    inverseDisplacement_positiveTwist_norm]

theorem realCuspVector_continuous : Continuous realCuspVector := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 1
  · exact (continuous_apply 0).neg

theorem normalizedPosition_eq_zero_of_time_eq_zero {x : Space} (hx : time x = 0) :
    normalizedPosition C₀ x = 0 := by
  have hp : position x = 0 := by
    ext i
    simp only [position, hx, norm_zero, Real.log_zero, div_zero, Pi.zero_apply]
  rw [normalizedPosition, hp, inverseDisplacement_zero, map_zero]

theorem normalizedPosition_continuousAt {ε : ℝ} (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) {x : Space}
    (hx : time x ≠ 0) (ht : ‖time x‖ < ε) :
    ContinuousAt (normalizedPosition C₀) x := by
  have htpos : 0 < ‖time x‖ := norm_pos_iff.mpr hx
  have hlog : Real.log ‖time x‖ < 0 := Real.log_neg htpos (ht.trans hε1)
  have hinv := inverseDisplacement_continuousAt (positiveTwist C₀)
    (fun _ _ => continuousAt_const) hlog (hR _ htpos ht) (position x)
  have hp : ContinuousAt (fun y : Space => (time y, position y)) x :=
    time_holomorphic.continuous.continuousAt.prodMk (position_continuousAt hx hlog.ne)
  exact realCuspVector_continuous.continuousAt.comp
    (ContinuousAt.comp (f := fun y : Space => (time y, position y))
      (g := fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement (positiveTwist C₀) p.1 p.2)
      hinv hp)

/-- Exact covariance for the original positive-twist action, with its
original integral labels. -/
theorem normalizedPosition_twistedTranslate {ε : ℝ} (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) (v : Fin 2 → ℤ) {x : Space}
    (hx : time x ≠ 0) (ht : ‖time x‖ < ε) :
    normalizedPosition C₀ (twistedTranslate (positiveTwist C₀) v x) =
      normalizedPosition C₀ x + CuspHoneycombTiling.latticePoint (cuspVector v) := by
  have htpos : 0 < ‖time x‖ := norm_pos_iff.mpr hx
  have hlog : Real.log ‖time x‖ < 0 := Real.log_neg htpos (ht.trans hε1)
  unfold normalizedPosition
  rw [time_twistedTranslate,
    position_twistedTranslate_displacement (positiveTwist C₀) v
      ((mem_openTorus_iff x).mpr hx) hlog.ne,
    inverseDisplacement_add,
    inverseDisplacement_displacement (positiveTwist C₀) hlog (hR _ htpos ht),
    map_add, realCuspVector_latticeReal]
  rfl

theorem normalizedPosition_continuousOn {ε : ℝ} (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    ContinuousOn (normalizedPosition C₀) {x : Space | time x ≠ 0 ∧ ‖time x‖ < ε} := by
  intro x hx
  exact (normalizedPosition_continuousAt C₀ hε1 hR hx.1 hx.2).continuousWithinAt

/-- The uniform bound also holds at central points, where the total
normalized position is zero. -/
theorem normalizedPosition_norm_le {ε : ℝ} (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) {x : Space} (ht : ‖time x‖ < ε) :
    ‖normalizedPosition C₀ x‖ ≤ 2 * ‖position x‖ := by
  by_cases hx : time x = 0
  · rw [normalizedPosition_eq_zero_of_time_eq_zero C₀ hx, norm_zero]
    positivity
  · have htpos : 0 < ‖time x‖ := norm_pos_iff.mpr hx
    rw [normalizedPosition, realCuspVector_norm]
    exact inverseDisplacement_norm_le (positiveTwist C₀)
      (Real.log_neg htpos (ht.trans hε1)) (hR _ htpos ht) (position x)

theorem normalizedPosition_locally_bounded {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) {x : Space} (ht : ‖time x‖ < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ y in 𝓝 x,
      ‖time y‖ < ε ∧ ‖normalizedPosition C₀ y‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := position_locally_bounded hε hε1 ht
  refine ⟨2 * B, mul_nonneg (by norm_num) hB, ?_⟩
  filter_upwards [hbound] with y hy
  exact ⟨hy.1, (normalizedPosition_norm_le C₀ hε1 hR hy.1).trans
    (mul_le_mul_of_nonneg_left hy.2 (by norm_num))⟩

/-- Actual norm-height paired with the normalized planar position. -/
def heightPosition (x : Space) : ℝ × (Fin 2 → ℝ) :=
  (‖time x‖, normalizedPosition C₀ x)

@[simp] theorem heightPosition_fst (x : Space) : (heightPosition C₀ x).1 = ‖time x‖ := rfl

@[simp] theorem heightPosition_snd (x : Space) :
    (heightPosition C₀ x).2 = normalizedPosition C₀ x := rfl

theorem heightPosition_continuousAt {ε : ℝ} (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) {x : Space}
    (hx : time x ≠ 0) (ht : ‖time x‖ < ε) : ContinuousAt (heightPosition C₀) x :=
  time_holomorphic.continuous.continuousAt.norm.prodMk
    (normalizedPosition_continuousAt C₀ hε1 hR hx ht)

theorem heightPosition_continuousOn {ε : ℝ} (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    ContinuousOn (heightPosition C₀) {x : Space | time x ≠ 0 ∧ ‖time x‖ < ε} := by
  intro x hx
  exact (heightPosition_continuousAt C₀ hε1 hR hx.1 hx.2).continuousWithinAt

theorem heightPosition_twistedTranslate {ε : ℝ} (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) (v : Fin 2 → ℤ) {x : Space}
    (hx : time x ≠ 0) (ht : ‖time x‖ < ε) :
    heightPosition C₀ (twistedTranslate (positiveTwist C₀) v x) =
      (‖time x‖, normalizedPosition C₀ x + CuspHoneycombTiling.latticePoint (cuspVector v)) := by
  rw [heightPosition, time_twistedTranslate,
    normalizedPosition_twistedTranslate C₀ hε1 hR v hx ht]

section ClosedPositive

variable {ε η : ℝ} (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε) (hηε : η < ε)

include hε1 hR hηε

theorem normalizedPosition_closedPositive_continuousAt {q : ClosedPositiveTube η}
    (hq : time (q.1 : Space) ≠ 0) :
    ContinuousAt (fun r : ClosedPositiveTube η => normalizedPosition C₀ (r.1 : Space)) q :=
  ContinuousAt.comp (f := fun r : ClosedPositiveTube η => (r.1 : Space))
    (g := normalizedPosition C₀)
    (normalizedPosition_continuousAt C₀ hε1 hR hq (q.2.trans_lt hηε))
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

theorem normalizedPosition_closedPositive_continuousOn :
    ContinuousOn (fun q : ClosedPositiveTube η => normalizedPosition C₀ (q.1 : Space))
      {q | time (q.1 : Space) ≠ 0} := by
  intro q hq
  exact (normalizedPosition_closedPositive_continuousAt C₀ hε1 hR hηε hq).continuousWithinAt

theorem normalizedPosition_closedPositive_twistedTranslate (v : Fin 2 → ℤ)
    {q : ClosedPositiveTube η} (hq : time (q.1 : Space) ≠ 0) :
    normalizedPosition C₀ ((closedPositiveTranslate C₀ η v q).1 : Space) =
      normalizedPosition C₀ (q.1 : Space) + CuspHoneycombTiling.latticePoint (cuspVector v) :=
  normalizedPosition_twistedTranslate C₀ hε1 hR v hq (q.2.trans_lt hηε)

theorem heightPosition_closedPositive_continuousAt {q : ClosedPositiveTube η}
    (hq : time (q.1 : Space) ≠ 0) :
    ContinuousAt (fun r : ClosedPositiveTube η => heightPosition C₀ (r.1 : Space)) q :=
  ContinuousAt.comp (f := fun r : ClosedPositiveTube η => (r.1 : Space))
    (g := heightPosition C₀)
    (heightPosition_continuousAt C₀ hε1 hR hq (q.2.trans_lt hηε))
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

theorem heightPosition_closedPositive_continuousOn :
    ContinuousOn (fun q : ClosedPositiveTube η => heightPosition C₀ (q.1 : Space))
      {q | time (q.1 : Space) ≠ 0} := by
  intro q hq
  exact (heightPosition_closedPositive_continuousAt C₀ hε1 hR hηε hq).continuousWithinAt

end ClosedPositive

end Wikipedia.HopfProblem.CuspControlledRetraction
