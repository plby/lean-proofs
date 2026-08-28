import Wikipedia.HopfProblem.DegreeCollapseClosedMiddleIntersections
import Wikipedia.NoExoticSixSphere.SphereCylinderVector

/-!
# The closed middle spheres retain the original smooth core germs

On the open negative hemisphere the closed sphere maps are exactly the
original inverse Morse chart applied to the corresponding linear coordinate
plane and the sphere's tail. They are therefore smooth on that whole open
hemisphere. The critical pole lies in it.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

def negativeHemisphere : Set (Hemisphere.Sphere 3) := {x | x.val 0 < 0}

theorem negativeHemisphere_open : IsOpen negativeHemisphere :=
  isOpen_lt ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val) continuous_const

theorem middlePole_mem_negativeHemisphere : middlePole ∈ negativeHemisphere := by
  change -Hemisphere.radius (⟨0, mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball 3) < 0
  simp [Hemisphere.radius]

theorem smooth_tail : ContMDiff (𝓡 3) 𝓘(ℝ, Hemisphere.Ambient 3) ∞
    (Hemisphere.tail (n := 3)) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 4) = 3 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have he : (fun x : Hemisphere.Sphere 3 => NoExoticSixSphere.SphereCylinder.tail 2 x.val) =
      Hemisphere.tail := by
    funext x
    ext i
    rfl
  rw [← he]
  exact (NoExoticSixSphere.SphereCylinder.tail 2).contDiff.contMDiff.comp contMDiff_coe_sphere

namespace SeparatedSystem

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

theorem descendingSphere_negative_formula (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (x : Hemisphere.Sphere 3)
    (hx : x ∈ negativeHemisphere) :
    D.descendingSphere p hp x =
      CoreDisks.negativeFun (D.windows.data p) (D.negativeLinear p hp (Hemisphere.tail x)) :=
  SphereDiskGluing.map_of_nonpos _ _ _ x (le_of_lt hx)

theorem ascendingSphere_negative_formula (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (x : Hemisphere.Sphere 3)
    (hx : x ∈ negativeHemisphere) :
    D.ascendingSphere p hp x =
      CoreDisks.positiveFun (D.windows.data p) (D.positiveLinear p hp (Hemisphere.tail x)) :=
  SphereDiskGluing.map_of_nonpos _ _ _ x (le_of_lt hx)

theorem descendingSphere_smooth_negative (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    ContMDiffOn (𝓡 3) 𝓘(ℝ, E) ∞ (D.descendingSphere p hp) negativeHemisphere := by
  intro x hx
  let d := D.windows.data p
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (fun y => (d.radius • D.negativeLinear p hp (Hemisphere.tail y),
        (0 : d.chart.PositiveCoordinates))) := by
    have hc : ContDiff ℝ ∞ (fun v : Hemisphere.Ambient 3 => d.radius • D.negativeLinear p hp v) :=
      by fun_prop
    exact (hc.contMDiff.comp smooth_tail).prodMk_space contMDiff_const
  have ht := CoreDisks.negative_target d
    (StandardDiskCoordinates.disk (D.negativeLinear p hp) (Hemisphere.disk x))
  have hi := (d.chart.splitChart.contMDiffOn_invFun _ ht).contMDiffAt
    (d.chart.splitChart.open_target.mem_nhds ht)
  apply ((hi.comp x hs.contMDiffAt).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [negativeHemisphere_open.mem_nhds hx] with y hy
  exact D.descendingSphere_negative_formula p hp y hy

theorem ascendingSphere_smooth_negative (p : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) :
    ContMDiffOn (𝓡 3) 𝓘(ℝ, E) ∞ (D.ascendingSphere p hp) negativeHemisphere := by
  intro x hx
  let d := D.windows.data p
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (fun y => ((0 : d.chart.NegativeCoordinates),
        d.radius • D.positiveLinear p hp (Hemisphere.tail y))) := by
    have hc : ContDiff ℝ ∞ (fun v : Hemisphere.Ambient 3 => d.radius • D.positiveLinear p hp v) :=
      by fun_prop
    exact contMDiff_const.prodMk_space (hc.contMDiff.comp smooth_tail)
  have ht := CoreDisks.positive_target d
    (StandardDiskCoordinates.disk (D.positiveLinear p hp) (Hemisphere.disk x))
  have hi := (d.chart.splitChart.contMDiffOn_invFun _ ht).contMDiffAt
    (d.chart.splitChart.open_target.mem_nhds ht)
  apply ((hi.comp x hs.contMDiffAt).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [negativeHemisphere_open.mem_nhds hx] with y hy
  exact D.ascendingSphere_negative_formula p hp y hy

end SeparatedSystem
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
