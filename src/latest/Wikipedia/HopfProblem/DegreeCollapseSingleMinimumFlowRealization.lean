import Wikipedia.HopfProblem.DegreeCollapseSingleMinimumBranches
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization
import Wikipedia.HopfProblem.DegreeCollapsePrescribedFlowWindows

/-!
# An actual adapted system with both chosen one-handle branches at the minimum

Realize the constructed lower-level point motion by native holonomy. Every
critical field germ is retained. Rebuild separated surgery windows with the
exact resulting flow and the original signed charts. Both new attaching
points then flow to the unique minimum; every connection from the selected
one-handle to any other lower critical point is excluded.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.realize_unique_minimum_one_handle_branches
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (p q : criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (hunique : ∀ r : criticalPoints E f, nativeMorseIndex E f r = 0 → r = p) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ r : criticalPoints E f, ∀ᶠ x in 𝓝 r.val, T.field x = S.field x) ∧
      (∀ r, (T.data r).chart = (S.data r).chart) ∧
      (∀ w : sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
        Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val)) ∧
      ∀ r : criticalPoints E f, r ≠ q → r ≠ p → ∀ x,
        ¬(Tendsto (fun t => T.flow t x) atBot (𝓝 q.val) ∧
          Tendsto (fun t => T.flow t x) atTop (𝓝 r.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, hpq, hall⟩ := S.place_one_handle_in_unique_minimum_basin hf p q hone hunique
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := exists_distinct_unitSphere_points_of_finrank_one hi
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain ⟨ρ, C, W, V, H, G, -, -, -, -, -, -, hgeometry,
      hV, hG, hzero, hdesc, hgerms, -, hend, -, hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  have hVz : ∀ x ∈ criticalPoints E f, V x = 0 := fun x hx => (hzero x).mpr (S.zero x hx)
  obtain ⟨hback, hforward⟩ := FlowSuspension.whole_level_basins_of_holonomy
    S.flow H G Subtype.val d (fun x z => (hgeometry x).2.1 z)
      (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
      Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔
        x ∈ range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
      Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val) :=
    (hforward _ p.val).mpr (hall w)
  have hno (r : criticalPoints E f) (hrq : r ≠ q) (hrp : r ≠ p) (x : M) :
      ¬(Tendsto (fun t => G t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => G t x) atTop (𝓝 r.val)) := by
    intro hx
    have hmono := FlowConstruction.antitone_flow_height hf G hG hVz hdesc x
    have hle : f r ≤ f q :=
      (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.2) 0).trans
        (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.1) 0)
    have hrq' : f r < f q := lt_of_le_of_ne hle
      (fun h => hrq (Subtype.ext (S.distinct r.property q.property h)))
    have hrlow : f r < S.toSurgeryWindows.lower q :=
      (S.toSurgeryWindows.value_lt_upper r).trans (S.separated r q hrq')
    obtain ⟨t, ht⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous
      hx.1 hx.2 (S.toSurgeryWindows.lower_lt_value q) hrlow
    let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
    have hzq : Tendsto (fun s => G s z) atBot (𝓝 q.val) :=
      (flow_time_atBot_limit_iff G t x q.val).mpr hx.1
    have hzr : Tendsto (fun s => G s z) atTop (𝓝 r.val) :=
      (flow_time_atTop_limit_iff G t x r.val).mpr hx.2
    obtain ⟨w, hw⟩ := (hbq z).mp hzq
    have hpz := hends w
    rw [hw] at hpz
    exact hrp (Subtype.ext (tendsto_nhds_unique hzr hpz))
  have hmodel (r : criticalPoints E f) :
      ∀ᶠ x in 𝓝 r.val, V x = (S.data r).chart.descentField x := by
    filter_upwards [hgerms r r.property, S.critical_model_germ r] with x hx hxs
    exact hx.trans hxs
  obtain ⟨T, hfield, hflow, hchart⟩ := exists_adapted_windows_with_prescribed_flow
    hf hm S.distinct hV G hG hVz hdesc (fun r => (S.data r).chart) hmodel
  refine ⟨T, ?_, hchart, ?_, ?_⟩
  · intro r
    rw [hfield]
    exact hgerms r r.property
  · intro w
    let z := (T.data q).surgery.attachingSphere w
    have hzq : Tendsto (fun t => T.flow t z.val) atBot (𝓝 q.val) :=
      (T.attaching_basin_iff hf q z).mpr ⟨w, rfl⟩
    obtain ⟨r₀, hr₀, r, hr, -, hrlim, hheight⟩ := FlowCancellation.exists_native_descent_endpoints
      hf T.smooth T.flow T.integral T.zero T.descent T.distinct z.val
    have hrq : (⟨r, hr⟩ : criticalPoints E f) ≠ q := by
      intro heq
      have hlt := (hheight ((T.data q).lower_regular z.val z.property)).1
      have hrval : r = q.val := congrArg Subtype.val heq
      rw [hrval, z.property] at hlt
      nlinarith [sq_nonneg (T.data q).radius]
    have hrp : (⟨r, hr⟩ : criticalPoints E f) = p := by
      by_contra hne
      apply hno ⟨r, hr⟩ hrq hne z.val
      rw [hflow] at hzq hrlim
      exact ⟨hzq, hrlim⟩
    exact (congrArg Subtype.val hrp) ▸ hrlim
  · intro r hrq hrp x
    rw [hflow]
    exact hno r hrq hrp x

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
