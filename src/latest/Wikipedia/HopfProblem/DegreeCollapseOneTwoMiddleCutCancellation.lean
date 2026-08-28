import Wikipedia.HopfProblem.DegreeCollapseHandleTradeTransverseLevelData
import Wikipedia.HopfProblem.DegreeCollapseUnitTransverseIsotopyRealization
import Wikipedia.HopfProblem.DegreeCollapseTwoEndpointConnectionExclusion
import Wikipedia.HopfProblem.DegreeCollapseFlowPreservingTransverseCancellation

/-!
# Actual one/two cancellation using a preserved middle level

Construct the transverse belt loop, place the new attaching section, realize
the unique complete connection and ambient basin tubes, and exclude every
other outgoing connection. Flow-preserving value descent then makes the
pair consecutive and native cancellation removes exactly those two points.
No circle, isotopy, connecting orbit, transversality, or consecutiveness is
an input; the original function supplies the middle-level index cut.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem cancel_one_two_pair_at_preserved_middle_cut
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : IsMorse E g) (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
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
    exists_handle_trade_transverse_level_data S T hf hg e hdim hfr hgr heq hhigh hlow
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

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
