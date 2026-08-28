import Wikipedia.HopfProblem.ToricProperAction

/-!
# Local control of the rescaled cusp position

The position is continuous off the central fibre, away from `|t| = 1`.
Its extension by zero on the central fibre need not be continuous, but it
is locally bounded throughout every sufficiently small tube.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

theorem position_continuousAt {x : Space} (hx : time x ≠ 0)
    (hlog : Real.log ‖time x‖ ≠ 0) : ContinuousAt position x := by
  have hxT : x ∈ openTorus := (mem_openTorus_iff x).mpr hx
  have hc : ContinuousAt torusCoordinates x :=
    torusCoordinates_holomorphic.continuousOn.continuousAt
      (openTorus_isOpen.mem_nhds hxT)
  have ht : ContinuousAt (fun y : Space => Real.log ‖time y‖) x :=
    ContinuousAt.comp (f := fun y : Space => ‖time y‖) (g := Real.log)
      (Real.continuousAt_log (norm_ne_zero_iff.mpr hx))
      time_holomorphic.continuous.continuousAt.norm
  apply continuousAt_pi.mpr
  intro i
  have hi : ContinuousAt (fun y : Space => torusCoordinates y i.castSucc) x :=
    (continuous_apply i.castSucc).continuousAt.comp hc
  have hli : ContinuousAt (fun y : Space => Real.log ‖torusCoordinates y i.castSucc‖) x :=
    ContinuousAt.comp (f := fun y : Space => ‖torusCoordinates y i.castSucc‖) (g := Real.log)
      (Real.continuousAt_log (norm_ne_zero_iff.mpr (torusCoordinates_nonzero hxT i.castSucc)))
      hi.norm
  exact hli.div ht hlog

theorem position_norm_le_on_chartNeighbourhood {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {s : Triangle} {n : ℕ} {x : Space} (hx : x ∈ chartNeighbourhood s n ε) :
    ‖position x‖ ≤ max 0 (positionBound s ((n : ℝ) + 2) ε) := by
  by_cases ht : time x = 0
  · have hp : position x = 0 := by
      ext i
      simp [position, ht]
    rw [hp, norm_zero]
    exact le_max_left _ _
  · obtain ⟨z, hz, rfl⟩ := hx
    have hzT : z ∈ torus := by
      rw [← inclusion_preimage_openTorus s]
      exact (mem_openTorus_iff _).mpr ht
    have hS : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact (position_norm_bound s hzT hS hε hε1 hz.2
      (fun j => (hz.1 j).le)).trans (le_max_right _ _)

theorem position_locally_bounded {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {x : Space} (ht : ‖time x‖ < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ y in 𝓝 x, ‖time y‖ < ε ∧ ‖position y‖ ≤ B := by
  obtain ⟨s, n, hx⟩ := chartNeighbourhood_cover ht
  refine ⟨max 0 (positionBound s ((n : ℝ) + 2) ε), le_max_left _ _, ?_⟩
  filter_upwards [(chartNeighbourhood_open s n ε).mem_nhds hx] with y hy
  exact ⟨chartNeighbourhood_time hy, position_norm_le_on_chartNeighbourhood hε hε1 hy⟩

end Wikipedia.HopfProblem.ToricSpace
