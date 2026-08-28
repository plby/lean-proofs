import Wikipedia.HopfProblem.DegreeCollapseCommonCutValueExchange
import Wikipedia.HopfProblem.DegreeCollapseTwoRegularCutWindows
import Wikipedia.HopfProblem.DegreeCollapseRegularBandReplacement

/-!
# An actual value exchange preserving both outer regions and the complete flow

Shrink native windows simultaneously away from the two regular cuts. The
actual no-connection rearrangement is confined between those windows.
Compact critical-value bounds retain the literal lower sublevel and upper
strict sublevel. New native windows retain the identical field and flow and
respect both cuts again, so the construction is repeatable.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_bounded_common_cut_value_exchange
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {a b : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (p q : criticalPoints E f) (hap : a < f p) (hpq : f p < f q) (hqb : f q < b)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hnoconnection : ∀ x, ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val))) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ InjOn g (criticalPoints E g) ∧
      g p = f q ∧ g q = f p ∧
      (∀ x ∈ criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f) ∧
      (∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
      (∀ k, nativeMorseCount E g k = nativeMorseCount E f k) ∧
      (∀ x, g x ≤ a ↔ f x ≤ a) ∧ (∀ x, g x = a ↔ f x = a) ∧
      (∀ x, g x < b ↔ f x < b) ∧ (∀ x, g x = b ↔ f x = b) ∧
      (∀ x, f x ≤ a → g =ᶠ[𝓝 x] f) ∧ (∀ x, b ≤ f x → g =ᶠ[𝓝 x] f) ∧
      (∀ x, g x = a → x ∉ criticalPoints E g) ∧
      (∀ x, g x = b → x ∉ criticalPoints E g) ∧
      ∃ T : AdaptedSurgeryWindows E g, T.field = S.field ∧ T.flow = S.flow ∧
        (∀ r : criticalPoints E g, g r < a → T.toSurgeryWindows.upper r < a) ∧
        (∀ r : criticalPoints E g, a < g r → a < T.toSurgeryWindows.lower r) ∧
        (∀ r : criticalPoints E g, g r < b → T.toSurgeryWindows.upper r < b) ∧
        ∀ r : criticalPoints E g, b < g r → b < T.toSurgeryWindows.lower r := by
  obtain ⟨W, _, _, _, _, _, hWa, hWb, _⟩ :=
    S.exists_same_flow_windows_avoiding_two_levels hf hm ha hb
  have hal := hWa p hap
  have hub := hWb q hqb
  obtain ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hdesc, hmodels,
      hindices, hcounts, hkeep⟩ :=
    exists_flow_preserving_value_exchange_in_windows W.toSurgeryWindows hf hm S.distinct
      S.smooth S.flow S.integral S.zero S.descent
      (fun x hx => ⟨(S.data ⟨x, hx⟩).chart, S.critical_model_germ ⟨x, hx⟩⟩)
      p q hpq hconsecutive hnoconnection
  have hout (x : M) (hx : f x ≤ W.toSurgeryWindows.lower p) : g =ᶠ[𝓝 x] f :=
    hkeep x (fun h => h.1.not_ge hx)
  have hbound (x : M) (hx : x ∈ criticalPoints E g)
      (hfx : W.toSurgeryWindows.lower p ≤ f x) : W.toSurgeryWindows.lower p ≤ g x := by
    by_cases hxp : x = p.val
    · rw [hxp, hgp]
      exact ((W.toSurgeryWindows.lower_lt_value p).trans hpq).le
    by_cases hxq : x = q.val
    · rw [hxq, hgq]
      exact (W.toSurgeryWindows.lower_lt_value p).le
    rw [(hothers x (hcrit ▸ hx) hxp hxq).self_of_nhds]
    exact hfx
  obtain ⟨hsub, hlevel, hlowgerm⟩ := lower_cuts_preserved_of_critical_bound
    hf.continuous hg hal hout hbound
  have huppergerm (x : M) (hx : b ≤ f x) : g =ᶠ[𝓝 x] f :=
    hkeep x (fun h => (not_lt_of_ge hx) (h.2.trans hub))
  have hvalues (x : M)
      (hx : f x ∈ Icc (W.toSurgeryWindows.lower p) (W.toSurgeryWindows.upper q))
      (hxc : x ∈ criticalPoints E g) :
      g x ∈ Ioo (W.toSurgeryWindows.lower p) (W.toSurgeryWindows.upper q) := by
    rcases surgery_pair_band_isolation W.toSurgeryWindows p q hconsecutive
      x (hcrit ▸ hxc) hx with he | he
    · rw [he, hgp]
      exact ⟨(W.toSurgeryWindows.lower_lt_value p).trans hpq,
        W.toSurgeryWindows.value_lt_upper q⟩
    · rw [he, hgq]
      exact ⟨W.toSurgeryWindows.lower_lt_value p,
        hpq.trans (W.toSurgeryWindows.value_lt_upper q)⟩
  have hstrict (x : M) : g x < b ↔ f x < b := by
    by_cases hx : f x ∈ Ioo (W.toSurgeryWindows.lower p) (W.toSurgeryWindows.upper q)
    · have hgx := RegularBandReplacement.mem_open_band_of_critical_values hf hg
        (fun y hy => (hkeep y hy).self_of_nhds) hvalues hx
      exact iff_of_true (hgx.2.trans hub) (hx.2.trans hub)
    · rw [(hkeep x hx).self_of_nhds]
  have hupperlevel (x : M) : g x = b ↔ f x = b := by
    constructor
    · intro hx
      have hfx : b ≤ f x := le_of_not_gt (fun h => ((hstrict x).mpr h).ne hx)
      exact (huppergerm x hfx).self_of_nhds.symm.trans hx
    · intro hx
      exact (huppergerm x hx.ge).self_of_nhds.trans hx
  have hga (x : M) (hx : g x = a) : x ∉ criticalPoints E g := by
    rw [hcrit]
    exact ha x ((hlevel x).mp hx)
  have hgb (x : M) (hx : g x = b) : x ∉ criticalPoints E g := by
    rw [hcrit]
    exact hb x ((hupperlevel x).mp hx)
  choose c hc using (fun x : criticalPoints E g => hmodels x x.property)
  obtain ⟨T₀, hfield₀, hflow₀, _⟩ := exists_adapted_windows_with_prescribed_flow
    hg hmg hinjg S.smooth S.flow S.integral (fun x hx => S.zero x (hcrit ▸ hx)) hdesc c hc
  obtain ⟨T, hfield, hflow, _, _, hbelowA, haboveA, hbelowB, haboveB⟩ :=
    T₀.exists_same_flow_windows_avoiding_two_levels hg hmg hga hgb
  exact ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hindices, hcounts,
    hsub, hlevel, hstrict, hupperlevel, hlowgerm, huppergerm, hga, hgb,
    T, hfield.trans hfield₀, hflow.trans hflow₀, hbelowA, haboveA, hbelowB, haboveB⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
