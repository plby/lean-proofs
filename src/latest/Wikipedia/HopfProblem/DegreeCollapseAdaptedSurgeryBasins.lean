import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryWindows
import Wikipedia.HopfProblem.DegreeCollapseNativeBeltBasinImage

/-!
# Whole basin sections of the constructed common surgery flow

The original attaching and belt spheres are exactly the backward and
forward basin sections in their actual regular levels. These identities
hold simultaneously for every critical point of the constructed system.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.attaching_basin_iff (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (x : (S.data p).LowerLevel) :
    Tendsto (fun t => S.flow t x) atBot (𝓝 p.val) ↔
      x ∈ range (S.data p).surgery.attachingSphere := by
  let d := S.data p
  have hh := native_attaching_core_basin_iff d.chart hf S.smooth S.flow S.integral
    d.radius d.radius_pos d.block (S.model_germ p)
    (fun y hy => S.descent y (d.lower_regular y hy)) x.property
  rw [d.attaching_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩,
    fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

open Classical in
theorem AdaptedSurgeryWindows.belt_basin_iff (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (x : (S.data p).UpperLevel) :
    Tendsto (fun t => S.flow t x) atTop (𝓝 p.val) ↔
      x ∈ range (S.data p).surgery.beltSphere := by
  let d := S.data p
  have hh := native_belt_core_basin_iff d.chart hf S.smooth S.flow S.integral
    d.radius d.radius_pos d.block (S.model_germ p)
    (fun y hy => S.descent y (d.upper_regular y hy)) x.property
  rw [d.belt_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩,
    fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

open Classical in
theorem AdaptedSurgeryWindows.critical_model_germ (S : AdaptedSurgeryWindows E f)
    (p : criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, S.field y = (S.data p).chart.descentField y := by
  let d := S.data p
  have hcenter : d.chart.splitChart.symm
      (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) = p.val := by
    rw [← d.chart.splitChart_center]
    exact d.chart.splitChart.left_inv' d.chart.splitChart_mem_source
  have hg := S.model_germ p (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates)
    ⟨mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos)),
      mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos))⟩
  rw [hcenter] at hg
  exact hg

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
