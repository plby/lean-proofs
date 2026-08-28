import Wikipedia.HopfProblem.DegreeCollapseMiddleNoConnections
import Wikipedia.HopfProblem.DegreeCollapseFlowPreservingValueExchange
import Wikipedia.HopfProblem.DegreeCollapseEqualNativeLevels

/-!
# Exchange middle critical values while preserving the literal common cut

The native canonical sphere excludes the selected connection. Rearrangement
uses the original pair window and retains the exact descending field and
complete flow. Compact minimum control excludes an excursion below that
window, so the original lower levels and sublevels are literally unchanged.
Fresh native windows retain this same flow and avoid the common cut.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {f g : M → ℝ}

theorem lower_cuts_preserved_of_critical_bound (hf : Continuous f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) {l a : ℝ} (ha : a < l)
    (hexterior : ∀ y, f y ≤ l → g =ᶠ[𝓝 y] f)
    (hcritical : ∀ y ∈ criticalPoints E g, l ≤ f y → l ≤ g y) :
    (∀ y, g y ≤ a ↔ f y ≤ a) ∧ (∀ y, g y = a ↔ f y = a) ∧
      ∀ y, f y ≤ a → g =ᶠ[𝓝 y] f := by
  have hbound := superlevel_bound_of_critical_bound hf hg
    (fun y hy => (hexterior y hy.le).self_of_nhds.trans hy) hcritical
  have hbelow (y : M) (hy : g y ≤ a) : f y ≤ l := by
    by_contra h
    exact (ha.trans_le (hbound y (le_of_not_ge h))).not_ge hy
  refine ⟨?_, ?_, fun y hy => hexterior y (hy.trans ha.le)⟩
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy)).self_of_nhds) ▸ hy
    · intro hy
      rw [(hexterior y (hy.trans ha.le)).self_of_nhds]
      exact hy
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy.le)).self_of_nhds).symm.trans hy
    · intro hy
      exact (hexterior y (hy ▸ ha.le)).self_of_nhds.trans hy

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

theorem AdaptedSurgeryWindows.exists_common_cut_value_exchange
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hq : nativeMorseIndex E f q = 3) (hal : a < S.toSurgeryWindows.lower p)
    (γ : C(S₂, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ,
      S.flow t (nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ InjOn g (criticalPoints E g) ∧
      g p = f q ∧ g q = f p ∧
      (∀ z, f z ∉ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
        g =ᶠ[𝓝 z] f) ∧
      (∀ z ∈ criticalPoints E f, z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
      (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
      (∀ k, nativeMorseCount E g k = nativeMorseCount E f k) ∧
      (∀ y, g y ≤ a ↔ f y ≤ a) ∧ (∀ y, g y = a ↔ f y = a) ∧
      (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
      (∀ y, g y = a → y ∉ criticalPoints E g) ∧
      ∃ T : AdaptedSurgeryWindows E g, T.field = S.field ∧ T.flow = S.flow ∧
        (∀ r : criticalPoints E g, g r < a → T.toSurgeryWindows.upper r < a) ∧
        ∀ r : criticalPoints E g, a < g r → a < T.toSurgeryWindows.lower r := by
  have hpband : f p ∈ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  have hnoconnection := S.no_connection_above_canonical_cut hf p q hpq hq
    (hal.trans (S.toSurgeryWindows.lower_lt_value p)) γ horbit
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdesc, hexterior, hpgerm, hqgerm,
      hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm S.smooth
      S.flow S.integral S.zero S.descent S.distinct (S.data p).chart (S.data q).chart
      (S.critical_model_germ p) (S.critical_model_germ q) hpband hqband hpq hqband hpband
      (surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hnoconnection
  have hinjg : InjOn g (criticalPoints E g) := by
    rw [hcrit]
    exact injOn_of_exchanged_values S.distinct p.property q.property hgp hgq
      (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels (r : criticalPoints E g) :
      ∃ c : SignedMorseChart (E := E) g r.val,
        ∀ᶠ y in 𝓝 r.val, S.field y = c.descentField y := by
    have hr : r.val ∈ criticalPoints E f := hcrit ▸ r.property
    by_cases hrp : r.val = p.val
    · obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field
        (S.data p).chart hpgerm
      rw [hrp]
      exact ⟨c, hc ▸ S.critical_model_germ p⟩
    by_cases hrq : r.val = q.val
    · obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field
        (S.data q).chart hqgerm
      rw [hrq]
      exact ⟨c, hc ▸ S.critical_model_germ q⟩
    obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_germ_preserving_field
      (S.data ⟨r.val, hr⟩).chart (hothers r hr hrp hrq)
    exact ⟨c, hc ▸ S.critical_model_germ ⟨r.val, hr⟩⟩
  have hout (y : M) (hy : f y ≤ S.toSurgeryWindows.lower p) : g =ᶠ[𝓝 y] f :=
    hexterior y (fun h => h.1.not_ge hy)
  have hbound (y : M) (hy : y ∈ criticalPoints E g)
      (hfy : S.toSurgeryWindows.lower p ≤ f y) : S.toSurgeryWindows.lower p ≤ g y := by
    by_cases hyp : y = p.val
    · rw [hyp, hgp]
      exact hqband.1.le
    by_cases hyq : y = q.val
    · rw [hyq, hgq]
      exact hpband.1.le
    rw [(hothers y (hcrit ▸ hy) hyp hyq).self_of_nhds]
    exact hfy
  obtain ⟨hsub, hlevel, hgerm⟩ := lower_cuts_preserved_of_critical_bound
    hf.continuous hg hal hout hbound
  have hga (y : M) (hy : g y = a) : y ∉ criticalPoints E g := by
    rw [hcrit]
    exact ha y ((hlevel y).mp hy)
  choose c hc using hnewmodels
  obtain ⟨T₀, hfield₀, hflow₀, -⟩ := exists_adapted_windows_with_prescribed_flow
    hg hmg hinjg S.smooth S.flow S.integral (fun x hx => S.zero x (hcrit ▸ hx))
      (fun x hx => hdesc x (hcrit ▸ hx)) c hc
  obtain ⟨T, hfield, hflow, -, hbelow, habove⟩ :=
    T₀.exists_same_flow_windows_avoiding_level hg hmg hga
  exact ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hexterior, hothers, hindices,
    nativeMorseCount_eq_of_preserved_indices hcrit hindices, hsub, hlevel, hgerm, hga,
    T, hfield.trans hfield₀, hflow.trans hflow₀, hbelow, habove⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
