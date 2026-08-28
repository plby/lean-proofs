import Wikipedia.HopfProblem.DegreeCollapseGeometricPrescribedColumnAddition

/-!
# The common-cut hypotheses persist under smaller surgery windows

The old regular band and isolation of the pivot exclude all critical
values up to the pivot value. Smaller radii keep its new lower window
above the same cut. Separation in the new system handles every higher
critical label without retaining the old upper window itself.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

theorem regular_below_pivot_of_regular_lower_band (S : SurgeryWindows E f)
    (q : criticalPoints E f) {a : ℝ}
    (hband : ∀ y, f y ∈ Icc a (S.lower q) → y ∉ criticalPoints E f) :
    ∀ y, f y ∈ Ico a (f q) → y ∉ criticalPoints E f := by
  intro y hy hcrit
  by_cases hlow : f y ≤ S.lower q
  · exact hband y ⟨hy.1, hlow⟩ hcrit
  · have heq : y = q.val := S.isolated q y hcrit
      ⟨(lt_of_not_ge hlow).le, hy.2.le.trans (S.value_lt_upper q).le⟩
    exact hy.2.ne (congrArg f heq)

theorem lower_window_le_of_radius_le (S T : SurgeryWindows E f)
    (q : criticalPoints E f) (hr : (T.data q).radius ≤ (S.data q).radius) :
    S.lower q ≤ T.lower q := by
  have hs : (T.data q).radius ^ 2 ≤ (S.data q).radius ^ 2 :=
    (sq_le_sq₀ (T.data q).radius_pos.le (S.data q).radius_pos.le).mpr hr
  exact sub_le_sub_left hs (f q)

theorem common_cut_band_of_smaller_radius (S T : SurgeryWindows E f)
    (q : criticalPoints E f) {a : ℝ}
    (hal : a < S.lower q)
    (hband : ∀ y, f y ∈ Icc a (S.lower q) → y ∉ criticalPoints E f)
    (hr : (T.data q).radius ≤ (S.data q).radius) :
    a < T.lower q ∧
      ∀ y, f y ∈ Icc a (T.lower q) → y ∉ criticalPoints E f := by
  refine ⟨hal.trans_le (lower_window_le_of_radius_le S T q hr), ?_⟩
  intro y hy
  exact regular_below_pivot_of_regular_lower_band S q hband y
    ⟨hy.1, hy.2.trans_lt (T.lower_lt_value q)⟩

theorem higher_window_separation_of_value_order (S T : SurgeryWindows E f)
    (q p : criticalPoints E f) (hhigh : S.upper q < f p) :
    T.upper q < f p :=
  (T.upper_lt_lower q p ((S.value_lt_upper q).trans hhigh)).trans (T.lower_lt_value p)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
