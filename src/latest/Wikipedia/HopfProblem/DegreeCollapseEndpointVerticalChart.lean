import Wikipedia.HopfProblem.DegreeCollapseCubicFlowCylinder
import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart
import Mathlib.Dynamics.Flow

/-!
# Endpoint flow coordinates with the original axis clock

The explicit cubic cylinder transports the vertical coordinate field to
the cubic field. Composing it with a clock-normalized native endpoint
chart gives actual regular flow coordinates. The chart's axis agrees
with the original complete orbit on a full germ at the constructed slice.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

/-- The actual cubic cylinder derivative sends vertical velocity to the cubic field. -/
theorem cubicFlowCylinder_pushforward_vertical (σ : Fin m → ℝ) (a : ℝ)
    (p : (Fin m → ℝ) × ℝ) :
    fderiv ℝ (cubicFlowCylinder σ a) p (0, 1) =
      cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a p) := by
  have hd := ((contDiff_cubicFlowCylinder σ a).differentiable (by simp) p).hasFDerivAt
    |>.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hd' := hasDerivAt_cubicFlowCylinder σ a p.1 p.2
  exact hd.unique hd'

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The normalized endpoint chart supplies an actual vertical field chart
whose whole axis germ has the original orbit's time parameter. -/
theorem exists_endpoint_vertical_chart (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel : ∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y)
    (F : Flow ℝ M) (x : M) {c r T : ℝ}
    (hbox : closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source)
    (hT : cubicFlowCylinder σ a (0, T) ∈ ball (c, (0 : Fin m → ℝ)) r)
    (haxis : ∀ t : ℝ, cubicFlowCylinder σ a (0, t) ∈
      closedBall (c, (0 : Fin m → ℝ)) r → Ψ (cubicFlowCylinder σ a (0, t)) = F t x) :
    ∃ A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E)
      ((Fin m → ℝ) × ℝ) M ∞,
      (0, T) ∈ A.source ∧ A.target ⊆ Ψ.target ∧
      (∀ p, A p = Ψ (cubicFlowCylinder σ a p)) ∧
      (∀ y ∈ A.target, V y = FlowConstruction.partialChartField A.symm
        (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y) ∧
      (fun t : ℝ => A (0, t)) =ᶠ[𝓝 T] (fun t => F t x) := by
  let C := cubicFlowCylinderChart σ ha
  let A := C.trans Ψ
  have hsource : (0, T) ∈ A.source := by
    change (0, T) ∈ univ ∧ C (0, T) ∈ Ψ.source
    exact ⟨mem_univ _, hbox (ball_subset_closedBall hT)⟩
  refine ⟨A, hsource, fun _ hy => hy.1, fun _ => rfl, ?_, ?_⟩
  · intro y hy
    have hpush (p : (Fin m → ℝ) × ℝ) (_ : p ∈ C.source) :
        fderiv ℝ C p (0, 1) = cubicDescent σ (-(a ^ 2)) (C p) :=
      cubicFlowCylinder_pushforward_vertical σ a p
    have hh := partialChartField_of_model_conjugacy C Ψ
      (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) (cubicDescent σ (-(a ^ 2))) hpush hy
    exact (hmodel y hy.1).trans hh.symm
  · have hcont : Continuous (fun t : ℝ => cubicFlowCylinder σ a (0, t)) :=
      (contDiff_cubicFlowCylinder σ a).continuous.comp (continuous_const.prodMk continuous_id)
    have hnear : ∀ᶠ t in 𝓝 T, cubicFlowCylinder σ a (0, t) ∈ ball (c, (0 : Fin m → ℝ)) r :=
      hcont.continuousAt.eventually (isOpen_ball.mem_nhds hT)
    filter_upwards [hnear] with t ht
    exact haxis t (ball_subset_closedBall ht)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
