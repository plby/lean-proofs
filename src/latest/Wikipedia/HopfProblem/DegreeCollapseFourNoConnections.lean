import Wikipedia.HopfProblem.DegreeCollapseMiddleNoConnections
import Wikipedia.HopfProblem.DegreeCollapseCanonicalFourFamily

/-!
# Original four-handle basin sections exclude connections above the common cut

A putative connecting orbit crosses the higher point's native attaching
level. Its original sphere parameter then transports to the common cut.
The same forward endpoint cannot lie above that cut under a descending
flow. This supplies the no-connection hypothesis needed to rearrange
middle critical values while keeping the actual field.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem AdaptedSurgeryWindows.no_connection_above_canonical_four_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hpq : f p < f q) (hq : nativeMorseIndex E f q = 4)
    {a : ℝ} (hap : a < f p) (γ : C(S₃, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ,
      S.flow t (nativeIndexFourAttachingSphere S q hq x).val = (γ x).val) :
    ∀ x, ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)) := by
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  let e := SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 3
  intro x hx
  have hplower : f p < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq)
  obtain ⟨t, ht⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hx.1 hx.2 (S.toSurgeryWindows.lower_lt_value q) hplower
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Tendsto (fun s => S.flow s y.val) atBot (𝓝 q.val) :=
    (flow_time_atBot_limit_iff S.flow t x q.val).mpr hx.1
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  obtain ⟨z, hz⟩ := e.surjective u
  have hpoint : nativeIndexFourAttachingSphere S q hq z = y := by
    change (S.data q).surgery.attachingSphere (e z) = y
    exact (congrArg (S.data q).surgery.attachingSphere (show e z = u from hz)).trans hu
  obtain ⟨s, hs⟩ := horbit z
  rw [hpoint] at hs
  have hyforward : Tendsto (fun v => S.flow v y.val) atTop (𝓝 p.val) :=
    (flow_time_atTop_limit_iff S.flow t x p.val).mpr hx.2
  have hγforward := (flow_time_atTop_limit_iff S.flow s y.val p.val).mpr hyforward
  rw [hs] at hγforward
  have hheight : Tendsto (fun v => f (S.flow v (γ z).val)) atTop (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hγforward
  have hh := (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
    (γ z).val).le_of_tendsto hheight 0
  have hpa : f p ≤ a := by simpa only [S.flow.map_zero_apply, (γ z).property] using hh
  exact not_le_of_gt hap hpa

theorem AdaptedSurgeryWindows.no_connection_above_four_basin_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hpq : f p < f q) (hq : nativeMorseIndex E f q = 4)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (hap : a < f p)
    (γ : C(S₃, {y : M // f y = a}))
    (hfull : ∀ y, y ∈ range γ ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 q.val)) :
    ∀ x, ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)) := by
  obtain ⟨δ, _, _, _, _, horbit, _⟩ :=
    S.exists_canonical_four_basin_sphere hf q hq ha γ
      (Hemisphere.point true ⟨0, by simp⟩) hfull
  exact S.no_connection_above_canonical_four_cut hf p q hpq hq hap δ horbit

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
