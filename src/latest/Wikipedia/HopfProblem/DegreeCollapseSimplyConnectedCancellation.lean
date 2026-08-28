import Wikipedia.HopfProblem.DegreeCollapseSimplyConnectedCircleIsotopy
import Wikipedia.HopfProblem.DegreeCollapseUniqueMinimumOneTwoCancellation

/-!
# Actual one/two handle cancellation under simple connectivity

The constructed middle-level placement supplies the unit transverse count.
Native holonomy realizes it as a unique actual complete connection, and
flow-preserving descent plus native cancellation remove exactly the two
critical points. A unique minimum constructs both one-handle branches and
all surgery windows. These are the existing geometric cancellation proofs
with their former homotopy-sphere filling replaced by simple connectivity.
No higher homology vanishing or sphere recognition is assumed.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected

section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem exists_handle_trade_transverse_level_data
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) atTop (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : criticalPoints E g, g z < g r → g z < a)
    (hnewlow : ∀ z : criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    let _ := RegularLevel.chartedSpace hg hgr
    ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // g y = a} {y : M // g y = a} ∞,
      IsotopicToIdentity P ∧
      {x : {y : M // g y = a} | Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) ∧
        Tendsto (fun t => T.flow t (P x).val) atTop (𝓝 q.val)}.ncard = 1 ∧
      ∃ (α : C(Hemisphere.Sphere 1, {y : M // g y = a})) (z₀ : Hemisphere.Sphere 1)
        (β : sphere (0 : (T.data q).chart.PositiveCoordinates) 1 → {y : M // g y = a})
        (v : sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ α ∧
        MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v ∧ β v = α z₀ ∧
        NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) α β z₀ v ∧
        (∀ z, Tendsto (fun t => T.flow t (α z).val) atBot (𝓝 r.val)) ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => T.flow t (P (β w)).val) atTop (𝓝 q.val)) ∧
        ∀ x : {y : M // g y = a}, Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) →
          Tendsto (fun t => T.flow t (P x).val) atTop (𝓝 m.val) ∨
          Tendsto (fun t => T.flow t (P x).val) atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  obtain ⟨δ, hδ, hδi, hδd, z₀, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, hendpoints⟩ :=
    T.exists_transverse_middle_belt_loop hg hdim m q hm hq u hbranches hqa hgr hnewlow
  obtain ⟨α, hα, -, -, hrange, P, hP, hplace, hplacement⟩ :=
    exists_new_attaching_circle_placement S T hf hg hdim hfr hgr heq hhigh hlow
      r har hgap δ hδ hδi hδd
  obtain ⟨β, hβ, hcross, htrans, hPβ⟩ := exists_transverse_sheet_of_circle_placement P
    (hα.mdifferentiableAt (by simp)) hβ₀ hplace hcross₀ htrans₀
  refine ⟨P, hP, unit_level_count_of_circle_placement T.flow P.toEquiv δ z₀ hplacement hsingle,
    α, z₀, β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hPβ w]
    exact hw
  · intro x hx
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz]
    exact hendpoints z

end

section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem cancel_one_two_pair_at_preserved_middle_cut
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : IsMorse E g) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (u : sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) atTop (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : criticalPoints E g, g z < g r → g z < a)
    (hnewlow : ∀ z : criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse E h ∧
      InjOn h (criticalPoints E h) ∧
      (criticalPoints E h).ncard + 2 = (criticalPoints E g).ncard ∧
      (∀ w, w ∈ criticalPoints E h ↔ w ∈ criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
      ∀ w ∈ criticalPoints E h, nativeMorseIndex E h w = nativeMorseIndex E g w := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  have hnegq : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨P, hP, hcount, α, z₀, β, v, hα, hβ, hcross, htrans, hαbasin, hβbasin, hends⟩ :=
    exists_handle_trade_transverse_level_data S T hf hg hdim hfr hgr heq hhigh hlow
      m q r hm hq hr u hbranches hqa har hgap hnewlow
  have hqcut : g q < a := (T.toSurgeryWindows.value_lt_upper q).trans_le hqa
  obtain ⟨V, G, hV, hG, hzero, hdesc, hgerms, hbackr, hforwardq, hunique, hback, hforward, htubes⟩ :=
    T.realize_unit_transverse_level_isotopy hg r q har hqcut hgr P hP hcount α β z₀ v
      (hα.mdifferentiableAt (by simp)) hβ hcross htrans
      (Filter.Eventually.of_forall hαbasin) hβbasin
  have hendsG (x : {y : M // g y = a})
      (hx : Tendsto (fun t => G t x.val) atBot (𝓝 r.val)) :
      Tendsto (fun t => G t x.val) atTop (𝓝 q.val) ∨
      Tendsto (fun t => G t x.val) atTop (𝓝 m.val) := by
    have hh := hends x ((hback x r.val).mp hx)
    exact (hh.imp ((hforward x m.val).mpr) ((hforward x q.val).mpr)).symm
  have hnoconnection := no_other_connections_of_two_level_endpoints G hg.continuous T.distinct
    r q m har hgap (FlowConstruction.antitone_flow_height hg G hG hzero hdesc) hendsG
  have hmodels : ∀ x ∈ criticalPoints E g, ∃ c : SignedMorseChart (E := E) g x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    refine ⟨(T.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, T.critical_model_germ ⟨x, hx⟩] with y hy hyt
    exact hy.trans hyt
  have hmq : g m < g q :=
    (T.forward_limit_below_regular_level hg (T.data q).lower_regular
      ((T.data q).surgery.attachingSphere u) (hbranches u)).trans (T.toSurgeryWindows.lower_lt_value q)
  obtain ⟨hC, hD, hC0, hD0, hCb, hDb, htransM⟩ := htubes
  exact cancel_transverse_pair_after_flow_preserving_descent hg hmg T.distinct
    (m := 5) (by omega) hV G hG hzero hdesc hmodels q m r hmq (hqcut.trans har)
    (by omega) hnoconnection hforwardq hbackr hunique hC hD hC0 hD0 hCb hDb htransM

end

section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem cancel_one_two_pair_at_unchanged_cut_of_unique_minimum
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : IsMorse E g) (hinjg : InjOn g (criticalPoints E g))
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (hminimum : ∀ z : criticalPoints E g, nativeMorseIndex E g z = 0 → z = m)
    (hqa : g q < a) (har : a < g r)
    (hgap : ∀ z : criticalPoints E g, g z < g r → g z < a)
    (hnewlow : ∀ z : criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse E h ∧
      InjOn h (criticalPoints E h) ∧
      (criticalPoints E h).ncard + 2 = (criticalPoints E g).ncard ∧
      (∀ w, w ∈ criticalPoints E h ↔ w ∈ criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
      ∀ w ∈ criticalPoints E h, nativeMorseIndex E h w = nativeMorseIndex E g w := by
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨U, -, -, hbranchesU, -⟩ :=
    T₀.realize_unique_minimum_one_handle_branches hg hmg m q hq hminimum
  obtain ⟨T, -, hflow, -, hbelow, -⟩ := U.exists_same_flow_windows_avoiding_level hg hmg hgr
  have hbranches := U.attaching_branches_of_same_flow T hg m q hflow hbranchesU
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  obtain ⟨u, v, huv⟩ := exists_distinct_unitSphere_points_of_finrank_one hneg
  exact cancel_one_two_pair_at_preserved_middle_cut S T hf hg hmg hdim hfr hgr heq
    hhigh hlow m q r hm hq hr u hbranches (hbelow q hqa).le har hgap hnewlow

end

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected
