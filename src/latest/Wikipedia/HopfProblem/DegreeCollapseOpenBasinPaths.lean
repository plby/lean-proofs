import Wikipedia.HopfProblem.DegreeCollapseDenseMinimumBasins
import Wikipedia.HopfProblem.DegreeCollapseBasinSublevelPaths

/-!
# Paths in the actual open basin of a minimum

A finite flow segment reaches a path-component neighborhood of its limit.
Flow invariance keeps that entire segment in the basin. Thus every point in
an open attracting basin containing its equilibrium is joined to the actual
equilibrium inside the basin. The native minimum model supplies openness.
-/

noncomputable section

open Set Filter Function Topology
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem joinedIn_open_forward_basin
    {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    (F : Flow ℝ X) (p : X)
    (hopen : IsOpen {x : X | Tendsto (fun t => F t x) atTop (𝓝 p)})
    (hp : Tendsto (fun t => F t p) atTop (𝓝 p))
    {x : X} (hx : Tendsto (fun t => F t x) atTop (𝓝 p)) :
    JoinedIn {y : X | Tendsto (fun t => F t y) atTop (𝓝 p)} x p := by
  let B : Set X := {y | Tendsto (fun t => F t y) atTop (𝓝 p)}
  have hC := pathComponentIn_mem_nhds (hopen.mem_nhds hp)
  obtain ⟨T, hT⟩ := (hx.eventually hC).exists
  have htail : JoinedIn B (F T x) p :=
    (show JoinedIn B p (F T x) from hT).symm
  let γ : Path x (F T x) := {
    toFun := fun u => F ((u : ℝ) * T) x
    continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
    source' := by simp
    target' := by simp }
  have hsegment : JoinedIn B x (F T x) := by
    refine ⟨γ, fun u => ?_⟩
    exact (flow_time_atTop_limit_iff F ((u : ℝ) * T) x p).mpr hx
  exact hsegment.trans htail

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.joinedIn_minimum_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    {x y : M}
    (hx : Tendsto (fun t => S.flow t x) atTop (𝓝 p.val))
    (hy : Tendsto (fun t => S.flow t y) atTop (𝓝 p.val)) :
    JoinedIn {z : M | Tendsto (fun t => S.flow t z) atTop (𝓝 p.val)} x y := by
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  have hpp : Tendsto (fun t => S.flow t p.val) atTop (𝓝 p.val) := by
    have heq : (fun t => S.flow t p.val) = fun _ => p.val :=
      funext (fun t => FlowConstruction.flow_fixed_of_zero (S.smooth.of_le (by simp))
        S.flow S.integral (S.zero p p.property) t)
    rw [heq]
    exact tendsto_const_nhds
  have hopen := S.isOpen_minimum_forward_basin hf p hp
  exact (joinedIn_open_forward_basin S.flow p.val hopen hpp hx).trans
    (joinedIn_open_forward_basin S.flow p.val hopen hpp hy).symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
