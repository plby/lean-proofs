import Wikipedia.HopfProblem.DegreeCollapseMiddleFamilyValueExchange

/-!
# Lift the actual higher middle family to the level of a selected slide

Every common-cut point with a higher backward endpoint crosses the selected
upper level. Compactness and fullness of each old basin section force all
native attaching directions to reach the old cut; hence the lifted family
still covers every labelled basin on the new level. The exact old sphere
parameters are retained, along with smoothness, immersion and disjointness.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.backward_basin_reaches_compact_section
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (α : C(S₂, {y : M // f y = a}))
    (hfull : ∀ y, y ∈ range α ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val))
    {x : M} (hx : x ∉ criticalPoints E f)
    (hback : Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)) :
    x ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach := S.attaching_sphere_reaches_of_compact_basin_section hf p 2 ha α
    (Hemisphere.point true ⟨0, by simp⟩) hfull
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p hx hback
  let y : (S.data p).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Tendsto (fun s => S.flow s y.val) atBot (𝓝 p.val) :=
    (flow_time_atBot_limit_iff S.flow t x p.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p y).mp hyback
  apply (FlowCancellation.levelBasin_flow_iff S.flow f a t x).mp
  change y.val ∈ FlowCancellation.levelBasin S.flow f a
  rw [← hu]
  exact hreach u

theorem AdaptedSurgeryWindows.backward_basin_reaches_intermediate_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {x p : M} (hback : Tendsto (fun t => S.flow t x) atBot (𝓝 p))
    {b : ℝ} (hxb : f x < b) (hbp : b < f p) :
    x ∈ FlowCancellation.levelBasin S.flow f b := by
  have hh : Tendsto (fun t => f (S.flow t x)) atBot (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hback
  obtain ⟨t, ht⟩ := (hh.eventually (eventually_gt_nhds hbp)).exists
  apply mem_range_of_exists_le_of_exists_ge
    (hf.continuous.comp (S.flow.continuous continuous_id continuous_const))
  · refine ⟨0, ?_⟩
    change f (S.flow 0 x) ≤ b
    rw [S.flow.map_zero_apply]
    exact hxb.le
  · exact ⟨t, ht.le⟩

theorem AdaptedSurgeryWindows.transported_basin_image_of_reaching
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {X : Type} {a b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (p : M) (α : X → {y : M // f y = a}) (β : X → {y : M // f y = b})
    (hfull : ∀ y, y ∈ range α ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (α x).val = (β x).val)
    (hreach : ∀ y : {z : M // f z = b}, Tendsto (fun t => S.flow t y.val) atBot (𝓝 p) →
      y.val ∈ FlowCancellation.levelBasin S.flow f a) :
    ∀ y, y ∈ range β ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact (flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
      ((hfull (α z)).mp (mem_range_self z))
  · intro hy
    obtain ⟨s, hs⟩ := hreach y hy
    let x : {z : M // f z = a} := ⟨S.flow s y.val, hs⟩
    have hx : Tendsto (fun t => S.flow t x.val) atBot (𝓝 p) :=
      (flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hfull x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

theorem AdaptedSurgeryWindows.exists_higher_middle_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f) (j₀ : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3) (hpb : ∀ j, b < f (p j))
    (α : Fin n → C(S₂, {y : M // f y = a}))
    (hα : IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) :
    ∃ β : Fin n → C(S₂, {y : M // f y = b}),
      IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
      ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have hreach (j : Fin n) (x : S₂) :
      (α j x).val ∈ FlowCancellation.levelBasin S.flow f b := by
    apply S.backward_basin_reaches_intermediate_cut hf
      ((hfull j (α j x)).mp (mem_range_self x))
    · simpa only [(α j x).property] using hab
    · exact hpb j
  let x₀ : S₂ := Hemisphere.point true ⟨0, by simp⟩
  obtain ⟨t₀, ht₀⟩ := hreach j₀ x₀
  obtain ⟨β, hβs, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb (α j₀ x₀)
      ⟨S.flow t₀ (α j₀ x₀).val, ht₀⟩ (fun j => α j) hs
      (fun j => (he j).injective) hi hpair hreach
  refine ⟨fun j => ⟨β j, (hβs j).continuous⟩,
    ⟨hβs, hβe, hβi, hβpair, ?_⟩, horbit⟩
  intro j
  apply S.transported_basin_image_of_reaching hf hb (p j).val (α j) (β j)
    (hfull j) (horbit j)
  intro y hy
  exact S.backward_basin_reaches_compact_section hf (p j) (hp j) ha (α j) (hfull j)
    (hb y.val y.property) hy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
