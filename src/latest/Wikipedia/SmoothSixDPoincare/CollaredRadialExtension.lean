import Wikipedia.SmoothSixDPoincare.SphereDirection
import Wikipedia.SmoothSixDPoincare.RadialFillingTime

/-!
# A smooth Euclidean filling from a collared sphere nullhomotopy

The formula uses normalized direction and radial time. A constant top collar
makes it constant on an actual neighborhood of the origin. The bottom collar
makes it equal to the original sphere map outside a smaller disk, removing
the nonsmoothness of the clamped time at radius one.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.RadialFilling

variable {n : ℕ} {G K M : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace K M]
  {f : C(Hemisphere.Sphere n, M)} {c : M}
  (H : f.Homotopy (ContinuousMap.const _ c)) (b : Hemisphere.Sphere n)

/-- The actual radial filling, defined on the whole Euclidean space. -/
def filling (v : Hemisphere.Ambient (n + 1)) : M := H (radialTime v, direction b v)

theorem filling_eq_center
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c)
    {v : Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : filling H b v = c :=
  htop _ _ (three_quarters_le_radialTime hv)

theorem filling_eq_boundary
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    {v : Hemisphere.Ambient (n + 1)} (hv : 3 / 4 ≤ ‖v‖) :
    filling H b v = f (direction b v) := hbottom _ _ (radialTime_le_quarter hv)

/-- Agreement with the sphere map is exact, not merely up to homotopy. -/
theorem filling_on_sphere
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (v : Hemisphere.Sphere n) : filling H b v.1 = f v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  rw [filling_eq_boundary H b hbottom (by rw [hn]; norm_num), direction_of_mem_sphere]

/-- The radial filling is smooth everywhere, including the center and the unit boundary. -/
theorem contMDiff_filling (hf : ContMDiff (𝓡 n) J ∞ f)
    (hH : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) J ∞ H)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) :
    ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) J ∞ (filling H b) := by
  intro v
  by_cases hinner : ‖v‖ < 1 / 4
  · apply (contMDiffAt_const (c := c)).congr_of_eventuallyEq
    have hn : {w : Hemisphere.Ambient (n + 1) | ‖w‖ < 1 / 4} ∈ 𝓝 v :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hinner
    filter_upwards [hn] with w hw
    exact filling_eq_center H b htop (le_of_lt hw)
  · by_cases houter : 3 / 4 < ‖v‖
    · have hv : v ≠ 0 := norm_pos_iff.mp (by linarith)
      have hs := (hf (direction b v)).comp v (contMDiffAt_direction b hv)
      apply hs.congr_of_eventuallyEq
      have hn : {w : Hemisphere.Ambient (n + 1) | 3 / 4 < ‖w‖} ∈ 𝓝 v :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds houter
      filter_upwards [hn] with w hw
      exact filling_eq_boundary H b hbottom (le_of_lt hw)
    · have hv : 0 < ‖v‖ := by linarith [le_of_not_gt hinner]
      have hunit : ‖v‖ < 1 := by linarith [le_of_not_gt houter]
      exact (hH (radialTime v, direction b v)).comp v
        (f := fun w => (radialTime w, direction b w))
        ((contMDiffAt_radialTime hv hunit).prodMk (contMDiffAt_direction b (norm_pos_iff.mp hv)))

end Wikipedia.SmoothSixDPoincare.RadialFilling
