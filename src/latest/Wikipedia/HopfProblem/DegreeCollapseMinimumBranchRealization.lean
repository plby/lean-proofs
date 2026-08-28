import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchPlacement
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelIsotopyRealization
import Wikipedia.HopfProblem.DegreeCollapseWholeLevelBasinTransport
import Wikipedia.HopfProblem.DegreeCollapseConnectionSections

/-!
# Realize the two selected minimum branches in an actual descending flow

A regular interval around the original attaching level is constructed from
the finite critical values. The placed level isotopy is then realized by
the supported native holonomy theorem. Both endpoint basins are retained
exactly, and the selected one-handle has no connection to any other lower
critical point. All original critical field germs are preserved.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.regular_interval_around_level
    (S : AdaptedSurgeryWindows E f) {a : ℝ}
    (hreg : ∀ x, f x = a → x ∉ criticalPoints E f) :
    ∃ l u : ℝ, l < a ∧ a < u ∧
      ∀ x, f x ∈ Icc l u → x ∉ criticalPoints E f := by
  have ha : a ∉ f '' criticalPoints E f := by
    rintro ⟨x, hx, hfx⟩
    exact hreg x hfx hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((S.finite.image f).isClosed.isOpen_compl.mem_nhds ha)
  refine ⟨a - ε / 2, a + ε / 2, by linarith, by linarith, ?_⟩
  intro x hx hcrit
  have hh : f x ∈ ball a ε := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact hball hh ⟨x, hcrit, rfl⟩

open Classical in
theorem AdaptedSurgeryWindows.realize_one_handle_minimum_branches
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M)
      (p r : criticalPoints E f),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
      (∀ x ∈ criticalPoints E f, V x = 0) ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      (∀ x ∈ criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
      nativeMorseIndex E f p = 0 ∧ nativeMorseIndex E f r = 0 ∧ p ≠ r ∧
      f p < S.toSurgeryWindows.lower q ∧ f r < S.toSurgeryWindows.lower q ∧
      (∀ x : (S.data q).LowerLevel,
        Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔
          x ∈ range (S.data q).surgery.attachingSphere) ∧
      Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val) ∧
      Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) atTop (𝓝 r.val) ∧
      (∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val) ∨
        Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 r.val)) ∧
      ∀ j : criticalPoints E f, j ≠ q → j ≠ p → j ≠ r → ∀ x,
        ¬(Tendsto (fun t => G t x) atBot (𝓝 q.val) ∧
          Tendsto (fun t => G t x) atTop (𝓝 j.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, hall⟩ :=
    S.place_one_handle_in_distinct_minimum_basins hf q hone u v hnot
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain ⟨ρ, C, W, V, H, G, hρ, hρbound, hC, hCband, hW, hH, hgeometry,
      hV, hG, hzero, hdesc, hgerms, houtside, hend, hheight, hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  obtain ⟨hback, hforward⟩ := FlowSuspension.whole_level_basins_of_holonomy
    S.flow H G Subtype.val d (fun x z => (hgeometry x).2.1 z)
      (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
      Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔
        x ∈ range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
      Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val) ∨
      Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 r.val) :=
    (hall w).imp ((hforward _ p.val).mpr) ((hforward _ r.val).mpr)
  refine ⟨V, G, p, r, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc,
    hgerms, hp, hr, hpr, hpq, hrq, hbq, (hforward _ p.val).mpr hpu,
    (hforward _ r.val).mpr hrv, hends, ?_⟩
  intro j hjq hjp hjr x hx
  have hmono := FlowConstruction.antitone_flow_height hf G hG
    (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc x
  have hforwardHeight := hf.continuous.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuous.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f q := (hmono.le_of_tendsto hforwardHeight 0).trans
    (hmono.ge_of_tendsto hbackwardHeight 0)
  have hjq' : f j < f q := lt_of_le_of_ne hle
    (fun h => hjq (Subtype.ext (S.distinct j.property q.property h)))
  have hjlow : f j < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper j).trans (S.separated j q hjq')
  obtain ⟨t, ht⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous
    hx.1 hx.2 (S.toSurgeryWindows.lower_lt_value q) hjlow
  let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
  have hzq : Tendsto (fun s => G s z) atBot (𝓝 q.val) :=
    (flow_time_atBot_limit_iff G t x q.val).mpr hx.1
  have hzj : Tendsto (fun s => G s z) atTop (𝓝 j.val) :=
    (flow_time_atTop_limit_iff G t x j.val).mpr hx.2
  obtain ⟨w, hw⟩ := (hbq z).mp hzq
  have hh := hends w
  rw [hw] at hh
  rcases hh with hp' | hr'
  · exact hjp (Subtype.ext (tendsto_nhds_unique hzj hp'))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzj hr'))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
