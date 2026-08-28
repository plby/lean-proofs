import Wikipedia.HopfProblem.DegreeCollapseDualTradeTransverseData
import Wikipedia.HopfProblem.DegreeCollapseSublevelTransversePairCancellation
import Wikipedia.HopfProblem.DegreeCollapseUnitTransverseIsotopyRealization
import Wikipedia.HopfProblem.DegreeCollapseTwoEndpointConnectionExclusion

/-!
# Actual dual one/two cancellation at the original retained fiber

Construct the new adapted windows and their actual minimum branches,
transverse belt loop, attaching-circle placement, holonomy realization,
unique orbit, and native ambient basin tubes. Whole-level endpoint control
excludes every other outgoing connection. Bounded transverse cancellation
then fixes the entire upper germ and the literal strict sublevel.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem cancel_dual_one_two_pair_at_retained_fiber
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    {g : S.Space → ℝ} (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : IsMorse (Vector 7) g) (hinjg : InjOn g (criticalPoints (Vector 7) g)) {b c : ℝ}
    (hgr : ∀ y, g y = b → y ∉ criticalPoints (Vector 7) g)
    (heq : ∀ y, g y = b ↔ P.function y = a)
    (m q r : criticalPoints (Vector 7) g)
    (hm : nativeMorseIndex (Vector 7) g m = 0)
    (hq : nativeMorseIndex (Vector 7) g q = 1)
    (hr : nativeMorseIndex (Vector 7) g r = 2)
    (hbefore : ∀ p : criticalPoints (Vector 7) g, g p < g q → nativeMorseIndex (Vector 7) g p = 0)
    (hminimum : ∀ p : criticalPoints (Vector 7) g, g p < c →
      nativeMorseIndex (Vector 7) g p = 0 → p = m)
    (hqb : g q < b) (hbr : b < g r) (hrc : g r < c)
    (hgap : ∀ p : criticalPoints (Vector 7) g, g p < g r → g p < b)
    (hnewlow : ∀ p : criticalPoints (Vector 7) g, g p ≤ b → nativeMorseIndex (Vector 7) g p ≤ 2) :
    ∃ h : S.Space → ℝ, ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse (Vector 7) h ∧
      InjOn h (criticalPoints (Vector 7) h) ∧
      (criticalPoints (Vector 7) h).ncard + 2 = (criticalPoints (Vector 7) g).ncard ∧
      (∀ w, w ∈ criticalPoints (Vector 7) h ↔
        w ∈ criticalPoints (Vector 7) g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
      (∀ w ∈ criticalPoints (Vector 7) h,
        nativeMorseIndex (Vector 7) h w = nativeMorseIndex (Vector 7) g w) ∧
      (∀ w, c ≤ g w → h =ᶠ[𝓝 w] g) ∧ ∀ w, h w < c ↔ g w < c := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨T, _, _, _, hupper, _⟩ := T₀.exists_same_flow_windows_avoiding_level hg hmg hgr
  have hnegq : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  simp only [finrank_euclideanSpace_fin] at hsplit
  let _ : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 5 + 1) := ⟨by omega⟩
  obtain ⟨D, hmq, hD, hcount, α, z₀, β, v, hα, hβ, hcross, htrans,
      hαbasin, hβbasin, hends⟩ := P.exists_dual_trade_transverse_level_data A ha hfr hhigh hlow
    hg T hgr heq m q r hm hq hr (hqb.trans (hbr.trans hrc)) hbefore hminimum
      (hupper q hqb).le hbr hgap hnewlow
  obtain ⟨V, G, hV, hG, hzero, hdesc, hgerms, hbackr, hforwardq, hunique,
      hback, hforward, htubes⟩ := T.realize_unit_transverse_level_isotopy hg r q hbr hqb hgr
    D hD hcount α β z₀ v (hα.mdifferentiableAt (by simp)) hβ hcross htrans
      (Filter.Eventually.of_forall hαbasin) hβbasin
  have hendsG (x : {y : S.Space // g y = b})
      (hx : Tendsto (fun t => G t x.val) atBot (𝓝 r.val)) :
      Tendsto (fun t => G t x.val) atTop (𝓝 m.val) ∨
      Tendsto (fun t => G t x.val) atTop (𝓝 q.val) :=
    (hends x ((hback x r.val).mp hx)).imp ((hforward x m.val).mpr) ((hforward x q.val).mpr)
  have hnoconnection := no_other_connections_of_two_level_endpoints G hg.continuous
    hinjg r m q hbr hgap (FlowConstruction.antitone_flow_height hg G hG hzero hdesc) hendsG
  have hmodels : ∀ x ∈ criticalPoints (Vector 7) g,
      ∃ c : SignedMorseChart (E := Vector 7) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    refine ⟨(T.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, T.critical_model_germ ⟨x, hx⟩] with y hy hyt
    exact hy.trans hyt
  obtain ⟨hC, hE, hC0, hE0, hCb, hEb, htransM⟩ := htubes
  exact cancel_transverse_pair_below_cut hg hmg hinjg (m := 6) (by simp)
    hV G hG hzero hdesc hmodels q m r hmq (hqb.trans hbr) (by rw [hq, hr]) hrc
      (fun j hjr hjq hjm => hnoconnection j hjr hjm hjq)
      hforwardq hbackr hunique hC hE hC0 hE0 hCb hEb htransM

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
