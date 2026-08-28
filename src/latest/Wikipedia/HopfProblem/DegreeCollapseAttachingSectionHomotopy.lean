import Wikipedia.HopfProblem.DegreeCollapseCanonicalMiddleFamily

/-!
# Exact orbit transport gives a homotopy in the original sublevel

The signed hitting time is continuous on the actual regular-level basin.
For a downward transport it is positive, and its fractional-time flow
stays below the original source height. Thus the homotopy compares the
actual maps into the original sublevel, with the original parametrization.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} [TopologicalSpace X]

def levelSublevelMap (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    C({y : M // f y = a}, {y : M // f y ≤ b}) :=
  ⟨fun y => ⟨y.val, y.property.le.trans hab⟩, continuous_subtype_val.subtype_mk _⟩

theorem AdaptedSurgeryWindows.level_transport_homotopic_in_sublevel
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (g : C(X, {y : M // f y = b})) (γ : C(X, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (g x).val = (γ x).val) :
    Homotopic ((levelSublevelMap f le_rfl).comp g) ((levelSublevelMap f hab.le).comp γ) := by
  have hboundary (y : M) (hy : f y = a) : mvfderiv 𝓘(ℝ, E) f y (S.field y) < 0 :=
    S.descent y (ha y hy)
  have hreach (x : X) : (g x).val ∈ FlowCancellation.levelBasin S.flow f a := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, by rw [ht]; exact (γ x).property⟩
  let θ : X → ℝ := fun x => FlowCancellation.signedLevelTime S.flow f a (g x).val
  obtain ⟨hB, htime, -⟩ :=
    FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral hboundary
  have hθ : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f := fun y : X => (g y).val)
      (htime.continuousOn.continuousAt (hB.mem_nhds (hreach x)))
      (continuous_subtype_val.comp g.continuous).continuousAt
  have hhit (x : X) : f (S.flow (θ x) (g x).val) = a :=
    FlowCancellation.signedLevelTime_hits S.flow f a (hreach x)
  have hθpos (x : X) : 0 < θ x := by
    by_contra h
    have hh := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
      (g x).val (le_of_not_gt h)
    change f (S.flow 0 (g x).val) ≤ f (S.flow (θ x) (g x).val) at hh
    rw [S.flow.map_zero_apply, (g x).property, hhit x] at hh
    exact not_le_of_gt hab hh
  have hend (x : X) : S.flow (θ x) (g x).val = (γ x).val := by
    obtain ⟨t, ht⟩ := horbit x
    have hθt : θ x = t := FlowCancellation.signedLevelTime_eq_of_level S.flow hf.continuous
      (contMDiff_directionalDerivative hf S.smooth).continuous
      (fun y s => FlowConstruction.hasDerivAt_comp_integralCurve hf (S.integral y) s)
      hboundary (by rw [ht]; exact (γ x).property)
    rw [hθt]
    exact ht
  have hstay (u : unitInterval) (x : X) : f (S.flow ((u : ℝ) * θ x) (g x).val) ≤ b := by
    have hh := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
      (g x).val (mul_nonneg u.property.1 (hθpos x).le)
    simpa only [S.flow.map_zero_apply, (g x).property] using hh
  refine ⟨{
    toFun := fun z => ⟨S.flow ((z.1 : ℝ) * θ z.2) (g z.2).val, hstay z.1 z.2⟩
    continuous_toFun := (S.flow.continuous
      ((continuous_subtype_val.comp continuous_fst).mul (hθ.comp continuous_snd))
      (continuous_subtype_val.comp (g.continuous.comp continuous_snd))).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change S.flow ((0 : ℝ) * θ x) (g x).val = (g x).val
    simp
  · intro x
    apply Subtype.ext
    change S.flow ((1 : ℝ) * θ x) (g x).val = (γ x).val
    simpa only [one_mul] using hend x

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
