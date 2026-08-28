import Wikipedia.SmoothSixDPoincare.SphereTransportDiffeomorph
import Wikipedia.SmoothSixDPoincare.NativeChartTransition
import Wikipedia.SmoothSixDPoincare.SphereChartOrientation

/-!
# Exact outward-frame transport under the original sphere isometry

The actual centered coordinate transition satisfies the original chart
identity near zero. Differentiating that identity and adjoining the outward
radial column gives an equality of genuine linear frames. This will compare
the transition's determinant sign with the fixed outward-chart convention.
-/

noncomputable section

open Set Metric Topology Filter ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open SphereNormalCoordinates

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]

theorem ambient_chart_hasFDerivAt
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m)
      (EuclideanSpace ℝ (Fin m)) (sphere (0 : V) 1) ∞)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ c.source) :
    HasFDerivAt (fun u => (c u : V)) (fderiv ℝ (fun u => (c u : V)) z) z := by
  have hc : ContDiffOn ℝ ∞ (fun u => (c u : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact ((hc.contDiffAt (c.open_source.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt

variable (x y : sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y)

include he in
theorem chart_transition_eventually_eq :
    (fun u : EuclideanSpace ℝ (Fin m) =>
      (NativeParametrization.centered y
        (NativeChartTransition.chart x y (sphereDiffeomorph (n := m) R) u) : V)) =ᶠ[𝓝 0]
      (fun u : EuclideanSpace ℝ (Fin m) => R (NativeParametrization.centered x u : V)) := by
  let e := sphereDiffeomorph (n := m) R
  let T := NativeChartTransition.chart x y e
  have hS := T.open_source.mem_nhds (NativeChartTransition.zero_mem_source x y e he)
  filter_upwards [hS] with u hu
  have ht : e (NativeParametrization.centered x u) ∈
      (NativeParametrization.centered (D := EuclideanSpace ℝ (Fin m)) y).target := hu.2
  have h := (NativeParametrization.centered y).right_inv' ht
  exact congrArg Subtype.val h

theorem chart_transition_ambient_derivative :
    (fderiv ℝ (fun u => (NativeParametrization.centered y u : V)) 0).comp
      (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he).toContinuousLinearMap =
        R.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (fderiv ℝ (fun u => (NativeParametrization.centered x u : V)) 0) := by
  let e := sphereDiffeomorph (n := m) R
  let T := NativeChartTransition.chart x y e
  have hx := ambient_chart_hasFDerivAt (m := m) (NativeParametrization.centered x)
    (NativeParametrization.zero_mem_centered_source x)
  have hy := ambient_chart_hasFDerivAt (m := m) (NativeParametrization.centered y)
    (NativeParametrization.zero_mem_centered_source y)
  have hyT : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin m) =>
      (NativeParametrization.centered y u : V))
      (fderiv ℝ (fun u => (NativeParametrization.centered y u : V)) 0) (T 0) :=
    (NativeChartTransition.chart_zero x y e he).symm ▸ hy
  have hchain := hyT.comp 0 (NativeChartTransition.hasFDerivAt_chart x y e he)
  have hR := R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0 hx
  exact hchain.unique (hR.congr_of_eventuallyEq (chart_transition_eventually_eq x y R he))

theorem chart_radial_frame_comp :
    (chartRadialFrame (NativeParametrization.centered y) 0).comp
      ((ContinuousLinearMap.id ℝ ℝ).prodMap
        (NativeChartTransition.linear x y
          (sphereDiffeomorph (n := m) R) he).toContinuousLinearMap) =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (chartRadialFrame (NativeParametrization.centered x) 0) := by
  apply ContinuousLinearMap.ext
  intro z
  have hD := congrArg (fun A : EuclideanSpace ℝ (Fin m) →L[ℝ] V => A z.2)
    (chart_transition_ambient_derivative x y R he)
  have hcenter : R (NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) =
      (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) := by
    rw [NativeParametrization.centered_zero, NativeParametrization.centered_zero]
    exact congrArg Subtype.val he
  change z.1 • (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) +
      (fderiv ℝ (fun u => (NativeParametrization.centered y u : V)) 0)
        (NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he z.2) =
    R (z.1 • (NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) +
      (fderiv ℝ (fun u => (NativeParametrization.centered x u : V)) 0) z.2)
  rw [map_add, map_smul, hcenter]
  exact congrArg (fun v : V =>
    z.1 • (NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) + v) hD

end Wikipedia.SmoothSixDPoincare.SpherePoint
