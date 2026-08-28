import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBasins
import Wikipedia.SmoothSixDPoincare.MorseAttachingSphereSmooth
import Wikipedia.SmoothSixDPoincare.MorseBeltSphereSmooth

/-!
# The original Morse core spheres lie in the actual endpoint basins

When the original native field agrees with the Morse model on the whole
specified block, the actual attaching core converges backward and the
actual belt core converges forward. The maps are the original native
Morse core maps, with their explicit coordinates and level values.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem native_attaching_core_backward_limit (c : SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    Tendsto (fun t => F t (c.attachingCoreMap r hr hblock u)) atBot (𝓝 p) := by
  have hu : ‖(u : c.NegativeCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hn : ‖r • (u : c.NegativeCoordinates)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  have hcoords : (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)) ∈
      c.splitChart.target := by
    apply hblock
    constructor
    · rw [mem_closedBall_zero_iff, hn]
      linarith
    · rw [mem_closedBall_zero_iff, norm_zero]
      positivity
  have hcoord : c.splitChart (c.splitChart.symm
      (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates))) =
      (r • (u : c.NegativeCoordinates), 0) := c.splitChart.right_inv' hcoords
  have hh := native_morse_negative_plane_limit c hV F hF
    (x := c.splitChart.symm (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)))
    (show 0 < 2 * r by positivity) hblock hfield (c.splitChart.map_target' hcoords)
    (by rw [hcoord]; change ‖r • (u : c.NegativeCoordinates)‖ < 2 * r; rw [hn]; linarith)
    (by rw [hcoord])
  simpa only [c.attachingCoreMap_coe] using hh

open Classical in
theorem native_belt_core_forward_limit (c : SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    Tendsto (fun t => F t (c.beltCoreMap r hr hblock v)) atTop (𝓝 p) := by
  have hv : ‖(v : c.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have hn : ‖r • (v : c.PositiveCoordinates)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv, mul_one]
  have hcoords : ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates)) ∈
      c.splitChart.target := by
    apply hblock
    constructor
    · rw [mem_closedBall_zero_iff, norm_zero]
      positivity
    · rw [mem_closedBall_zero_iff, hn]
      linarith
  have hcoord : c.splitChart (c.splitChart.symm
      ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates))) =
      (0, r • (v : c.PositiveCoordinates)) := c.splitChart.right_inv' hcoords
  have hh := native_morse_positive_plane_limit c hV F hF
    (x := c.splitChart.symm ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates)))
    (show 0 < 2 * r by positivity) hblock hfield (c.splitChart.map_target' hcoords)
    (by rw [hcoord]; change ‖r • (v : c.PositiveCoordinates)‖ < 2 * r; rw [hn]; linarith)
    (by rw [hcoord])
  simpa only [c.beltCoreMap_coe] using hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
