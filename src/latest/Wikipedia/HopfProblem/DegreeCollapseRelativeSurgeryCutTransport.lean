import Wikipedia.HopfProblem.DegreeCollapseHolonomyCutCrossing

/-!
# Exact lower-cut transport and lower-basin preservation for a relative slide

The normalized exit section lies strictly above the selected critical
height. Any orbit reaching a regular cut below that height has already exited the
suspension, so its old-flow description uses exactly the endpoint level
diffeomorphism. Every backward basin at or below the selected critical
height is unchanged. These are pointwise geometric statements, not only
critical-label comparisons on the upper section.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_relative_surgery_cut_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (q : criticalPoints E f) (z : (S.data q).UpperLevel)
    (ε : criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀ (D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K P : Set (S.data q).UpperLevel), IsCompact K → SupportedRelativeIsotopy D K P →
      ∃ T : AdaptedSurgeryWindows E f,
        (∀ p, (T.data p).chart = (S.data p).chart) ∧
        (∀ p, (T.data p).radius < ε p) ∧
        (∀ p ∈ criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
        (∀ x : (S.data q).UpperLevel, ∀ p : M,
          Tendsto (fun t => T.flow t x.val) atBot (𝓝 p) ↔
            Tendsto (fun t => S.flow t x.val) atBot (𝓝 p)) ∧
        (∀ x : (S.data q).UpperLevel, ∀ p : M,
          Tendsto (fun t => T.flow t x.val) atTop (𝓝 p) ↔
            Tendsto (fun t => S.flow t (D x).val) atTop (𝓝 p)) ∧
        (∀ x ∈ P, range (fun t => T.flow t x.val) = range (fun t => S.flow t x.val)) ∧
        (∀ x : (S.data q).UpperLevel, ∀ {b : ℝ}, b < f q →
          (∀ y, f y = b → y ∉ criticalPoints E f) → ∀ y : {z : M // f z = b},
          (∃ t : ℝ, T.flow t x.val = y.val) ↔
            ∃ t : ℝ, S.flow t (D x).val = y.val) ∧
        ∀ p : M, f p ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 p) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 p)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 p) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t p) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t p) atTop (𝓝 v) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro D K P hK I
  obtain ⟨l, u, hl, hu, hband⟩ := S.regular_interval_around_level (S.data q).upper_regular
  have hql : f q < l := by
    by_contra h
    exact hband q ⟨le_of_not_gt h, (S.toSurgeryWindows.value_lt_upper q).le.trans hu.le⟩ q.property
  obtain ⟨r, C, W, V, H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry,
      hV, hG, hzero, hdesc, hgerms, houtside, hend, hheight, hleft, hright, hprotected⟩ :=
    FlowSuspension.exists_relative_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hu hband (S.data q).upper_regular z D K P hK I
  have hmodel (p : criticalPoints E f) : ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ := exists_adapted_windows_with_prescribed_flow_lt
    hf hm S.distinct hV G hG (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc
      (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback₀, hforward₀⟩ := FlowSuspension.whole_level_basins_of_holonomy
    S.flow H G Subtype.val D (fun x p => (hgeometry x).2.1 p)
      (fun x p => (hgeometry x).2.2 p) hend hleft hright
  have hback (x : (S.data q).UpperLevel) (p : M) :
      Tendsto (fun t => T.flow t x.val) atBot (𝓝 p) ↔
        Tendsto (fun t => S.flow t x.val) atBot (𝓝 p) := by
    rw [hflow]
    exact hback₀ x p
  have hforward (x : (S.data q).UpperLevel) (p : M) :
      Tendsto (fun t => T.flow t x.val) atTop (𝓝 p) ↔
        Tendsto (fun t => S.flow t (D x).val) atTop (𝓝 p) := by
    rw [hflow]
    exact hforward₀ x p
  have hlowexit {b : ℝ} (hb : b < f q) : b < S.toSurgeryWindows.upper q - r := by
    have hr' : r < S.toSurgeryWindows.upper q - l := hrbound
    linarith
  have htransport (x : (S.data q).UpperLevel) {b : ℝ} (hb : b < f q)
      (y : {z : M // f z = b})
      (hxy : ∃ t : ℝ, T.flow t x.val = y.val) : ∃ t : ℝ, S.flow t (D x).val = y.val := by
    obtain ⟨t, ht⟩ := hxy
    have hstart : f (T.flow 1 x.val) = S.toSurgeryWindows.upper q - r := by
      rw [hflow, hend, hheight]
      rfl
    have htone : 1 < t := by
      by_contra h
      have hh := (FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent
        x.val) (le_of_not_gt h)
      change f (T.flow 1 x.val) ≤ f (T.flow t x.val) at hh
      rw [hstart, ht, y.property] at hh
      exact (hlowexit hb).not_ge hh
    have heq : G t x.val = H t (D x).val := by
      calc
        G t x.val = G (t - 1) (G 1 x.val) := by rw [← G.map_add, sub_add_cancel]
        _ = H (t - 1) (H 1 (D x).val) := by
          rw [hend, hright (D x) (t - 1) (sub_nonneg.mpr htone.le)]
        _ = H t (D x).val := by rw [← H.map_add, sub_add_cancel]
    have hmem : H t (D x).val ∈ range (fun s => S.flow s (D x).val) :=
      (hgeometry (D x).val).1 ▸ mem_range_self t
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.trans (heq.symm.trans (hflow ▸ ht))⟩
  refine ⟨T, hcharts, hradii, ?_, hback, hforward, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = fun t => H t x.val := funext (hprotected x hx)
    rw [heq]
    exact (hgeometry x.val).1
  · intro x b hbq hb y
    refine ⟨htransport x hbq y, ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ := S.reaches_cut_of_forward_holonomy T hf
      (hbq.trans (S.toSurgeryWindows.value_lt_upper q)) hb (S.data q).upper_regular
      D hforward x y ⟨t, ht⟩
    let y' : {z : M // f z = b} := ⟨T.flow s x.val, hs⟩
    obtain ⟨v, hv⟩ := htransport x hbq y' ⟨s, rfl⟩
    have hshared : S.flow 0 y'.val = S.flow (v - t) y.val := by
      rw [S.flow.map_zero_apply, ← hv, ← ht, ← S.flow.map_add, sub_add_cancel]
    have heq : y'.val = y.val := native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (hb z hz)) y'.property y.property hshared
    exact ⟨s, heq⟩
  · intro p hp
    have hlow (y : M) (hy : f y ≤ l) : T.field y = W y := by
      rw [hfield]
      exact (houtside y (fun h => (hCband h).1.not_ge hy)).self_of_nhds
    have hb := lower_backward_basins_preserved S T hf hW H hH hgeometry hlow p
      (hp.trans hql.le)
    exact ⟨hb.1, hb.2, lower_forward_basins_preserved S T hf hW H hH
      (fun x v => (hgeometry x).2.1 v) hlow p (hp.trans hql.le)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
