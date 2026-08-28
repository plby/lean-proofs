import Wikipedia.HopfProblem.DegreeCollapseSupportedBasinPreservation

/-!
# Exact forward holonomy forces crossing of every reached lower regular cut

An old orbit reaching the target cut has a forward endpoint strictly below
it. The holonomy formula gives the same endpoint to the modified orbit,
while its backward endpoint lies above its source regular level. Hence
the modified orbit crosses that actual target cut, even across several
critical windows.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.reaches_cut_of_forward_holonomy
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (D : {y : M // f y = b} → {y : M // f y = b})
    (hforward : ∀ x : {y : M // f y = b}, ∀ p : M,
      Tendsto (fun t => T.flow t x.val) atTop (𝓝 p) ↔
        Tendsto (fun t => S.flow t (D x).val) atTop (𝓝 p))
    (x : {y : M // f y = b}) (y : {z : M // f z = a})
    (horbit : ∃ t : ℝ, S.flow t (D x).val = y.val) :
    x.val ∈ FlowCancellation.levelBasin T.flow f a := by
  obtain ⟨p, hp, q, hq, -, hytop, hyheight⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct y.val
  have hqa : f q < a := by
    simpa only [y.property] using (hyheight (ha y.val y.property)).1
  obtain ⟨t, ht⟩ := horbit
  have hDx : Tendsto (fun s => S.flow s (D x).val) atTop (𝓝 q) := by
    rw [← ht] at hytop
    exact (flow_time_atTop_limit_iff S.flow t (D x).val q).mp hytop
  have hxtop := (hforward x q).mpr hDx
  obtain ⟨r, hr, s, hs, hxback, -, hxheight⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral
      T.zero T.descent T.distinct x.val
  have hbr : b < f r := by
    simpa only [x.property] using (hxheight (hb x.val x.property)).2
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits T.flow hf.continuous
    hxback hxtop (hab.trans hbr) hqa

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
