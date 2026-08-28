import Wikipedia.HopfProblem.DegreeCollapseNativeCubicSegments
import Wikipedia.HopfProblem.DegreeCollapseNativeVerticalCylinderFlow

/-!
# Propagating an actual endpoint phase formula through the whole overlap

An exact regular-slice formula between the original endpoint and flow
charts extends to every other cubic point in the actual endpoint box.
The proved finite-segment box estimate and native uniqueness supply the
entire comparison domain. No additional trajectory-stays-in-chart input
is imposed on the connecting segment.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E Z M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem native_endpoint_phase_through_box (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hAsource : A.source = U ×ˢ univ)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΦmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y)
    (hAmodel : ∀ y ∈ A.target, V y =
      FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c r : ℝ} (hbox : closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source)
    (z : Fin m → ℝ) {q : Z} (hq : q ∈ U) {T v : ℝ}
    (hstart : cubicFlowCylinder σ a (z, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
    (hmatch : Φ (cubicFlowCylinder σ a (z, T)) = A (q, T + v)) :
    ∀ t : ℝ, cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r →
      Φ (cubicFlowCylinder σ a (z, t)) = A (q, t + v) := by
  intro t ht
  calc
    Φ (cubicFlowCylinder σ a (z, t)) = F (t - T) (Φ (cubicFlowCylinder σ a (z, T))) :=
      (native_cubic_flow_between_box_points σ ha Φ hV hΦmodel F hF hbox z hstart ht).symm
    _ = F (t - T) (A (q, T + v)) := congrArg (F (t - T)) hmatch
    _ = A (q, (T + v) + (t - T)) :=
      FlowSuspension.native_vertical_cylinder_flow A hAsource hV hAmodel F hF q hq (T + v) (t - T)
    _ = A (q, t + v) := congrArg (fun s : ℝ => A (q, s)) (by ring)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
