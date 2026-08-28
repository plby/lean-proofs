import Wikipedia.HopfProblem.DegreeCollapseBeltComplementLowerTransport
import Wikipedia.HopfProblem.DegreeCollapseSmoothBeltMeridian

/-!
# Native flow comparison of the entire two surgery complements

The original upper belt complement and lower attaching-sphere complement
are exactly the two domains of the native orbit transport. Both directions
are proved using actual endpoint limits and the separated surgery window.
The full parametrized meridian and its inverse are retained exactly.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] in
theorem AdaptedSurgeryWindows.attaching_complement_reaches_upper_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (y : (S.data p).LowerLevel)
    (hy : y ∉ range (S.data p).surgery.attachingSphere) :
    y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.upper p) := by
  obtain ⟨a, ha, b, hb, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct y.val
  have hyreg := (S.data p).lower_regular y.val y.property
  have habove : S.toSurgeryWindows.upper p < f a := by
    rcases lt_trichotomy (f p) (f a) with h | h | h
    · exact (S.separated p ⟨a, ha⟩ h).trans (S.toSurgeryWindows.lower_lt_value ⟨a, ha⟩)
    · have heq : a = p.val := S.distinct ha p.property h.symm
      subst a
      exact (hy ((S.attaching_basin_iff hf p y).mp hback)).elim
    · have hlo : f a < f y.val := by
        rw [y.property]
        exact (S.toSurgeryWindows.value_lt_upper ⟨a, ha⟩).trans (S.separated ⟨a, ha⟩ p h)
      exact (not_lt_of_ge hlo.le (hheights hyreg).2).elim
  have hbelow : f b < S.toSurgeryWindows.upper p := by
    exact (hheights hyreg).1.trans (y.property.trans_lt
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)))
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward habove hbelow

theorem AdaptedSurgeryWindows.upper_reaches_lower_iff_not_belt
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (y : (S.data p).UpperLevel) :
    y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) ↔
      y ∉ range (S.data p).surgery.beltSphere := by
  constructor
  · rintro ⟨t, ht⟩ hbelt
    let z : (S.data p).LowerLevel := ⟨S.flow t y.val, ht⟩
    have hforward := (S.belt_basin_iff hf p y).mpr hbelt
    have hz : Tendsto (fun s => S.flow s z.val) atTop (𝓝 p.val) :=
      (flow_time_atTop_limit_iff S.flow t y.val p.val).mpr hforward
    have hlt := S.forward_limit_below_regular_level hf (S.data p).lower_regular z hz
    exact (S.toSurgeryWindows.lower_lt_value p).not_gt hlt
  · exact S.belt_complement_reaches_lower_level hf p y

omit [FiniteDimensional ℝ E] in
theorem AdaptedSurgeryWindows.lower_reaches_upper_iff_not_attaching
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (y : (S.data p).LowerLevel) :
    y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.upper p) ↔
      y ∉ range (S.data p).surgery.attachingSphere := by
  constructor
  · rintro ⟨t, ht⟩ hattaching
    let z : (S.data p).UpperLevel := ⟨S.flow t y.val, ht⟩
    have hback := (S.attaching_basin_iff hf p y).mpr hattaching
    have hz : Tendsto (fun s => S.flow s z.val) atBot (𝓝 p.val) :=
      (flow_time_atBot_limit_iff S.flow t y.val p.val).mpr hback
    obtain ⟨a, _, _, _, hback', _, hheights⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
        S.zero S.descent S.distinct z.val
    have heq : a = p.val := tendsto_nhds_unique hback' hz
    have hlt := (hheights ((S.data p).upper_regular z.val z.property)).2
    rw [heq, z.property] at hlt
    exact (S.toSurgeryWindows.value_lt_upper p).not_gt hlt
  · exact S.attaching_complement_reaches_upper_level hf p y

theorem AdaptedSurgeryWindows.exists_native_surgery_complement_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    (u : sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    ∃ D : PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data p).UpperLevel (S.data p).LowerLevel ∞,
      D.source = (range (S.data p).surgery.beltSphere)ᶜ ∧
      D.target = (range (S.data p).surgery.attachingSphere)ᶜ ∧
      (∀ x ∈ D.source, ∃ t : ℝ, S.flow t x.val = (D x).val) ∧
      ∀ (s : unitInterval), 0 < (s : ℝ) →
        ∀ w : sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
          D (nativeUpperMeridian S p v s w) = nativeLowerMeridian S p v s w ∧
          D.symm (nativeLowerMeridian S p v s w) = nativeUpperMeridian S p v s w := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  obtain ⟨D, hsource, htarget, horbit⟩ := S.exists_native_level_basin_transport hf
    (S.data p).upper_regular (S.data p).lower_regular
    ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u)
  have hs : D.source = (range (S.data p).surgery.beltSphere)ᶜ := by
    rw [hsource]
    ext x
    exact S.upper_reaches_lower_iff_not_belt hf p x
  have ht : D.target = (range (S.data p).surgery.attachingSphere)ᶜ := by
    rw [htarget]
    ext x
    exact S.lower_reaches_upper_iff_not_attaching hf p x
  refine ⟨D, hs, ht, horbit, ?_⟩
  intro s hspos w
  have hx : nativeUpperMeridian S p v s w ∈ D.source := by
    rw [hs]
    exact nativeUpperMeridian_avoids_belt S p v s hspos w
  obtain ⟨t, htflow⟩ := horbit _ hx
  have hpassage := nativeUpperMeridian_flow S p v s hspos w
  have hshared : S.flow 0 (D (nativeUpperMeridian S p v s w)).val =
      S.flow (t - BeltPassage.time s) (nativeLowerMeridian S p v s w).val := by
    rw [S.flow.map_zero_apply, ← htflow, ← hpassage, ← S.flow.map_add, sub_add_cancel]
  have heq : D (nativeUpperMeridian S p v s w) = nativeLowerMeridian S p v s w := by
    apply Subtype.ext
    exact native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z ((S.data p).lower_regular z hz))
      (D (nativeUpperMeridian S p v s w)).property (nativeLowerMeridian S p v s w).property hshared
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact D.left_inv' hx

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
