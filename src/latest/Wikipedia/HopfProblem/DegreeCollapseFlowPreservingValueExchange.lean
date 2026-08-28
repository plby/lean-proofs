import Wikipedia.HopfProblem.DegreeCollapseMorseChartFieldGerms
import Wikipedia.HopfProblem.DegreeCollapseNoConnectionMorseRearrangement
import Wikipedia.HopfProblem.DegreeCollapseMorseValueExchange
import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairBands

/-!
# Adjacent value exchange retaining the very same field and flow

The isolated pair band is constructed from the current excellent function.
No-connection rearrangement changes its values, while the restricted shifted
charts retain every critical model field exactly. Thus the original complete
flow and all endpoint geometry are available for the next exchange.
The fixed-window version additionally retains the entire exterior germ;
the original window-existence interface follows by forgetting that data.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem exists_flow_preserving_value_exchange_in_windows (S : SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels : ∀ x ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hnoconnection : ∀ x, ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => F t x) atTop (𝓝 p.val))) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ InjOn g (criticalPoints E g) ∧
      g p = f q ∧ g q = f p ∧
      (∀ x ∈ criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f) ∧
      (∀ x, x ∉ criticalPoints E g → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
      (∀ x ∈ criticalPoints E g, ∃ c : SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
      (∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
      (∀ k, nativeMorseCount E g k = nativeMorseCount E f k) ∧
      ∀ x, f x ∉ Ioo (S.lower p) (S.upper q) → g =ᶠ[𝓝 x] f := by
  obtain ⟨cp, hcp⟩ := hmodels p p.property
  obtain ⟨cq, hcq⟩ := hmodels q q.property
  have hp : f p ∈ Ioo (S.lower p) (S.upper q) :=
    ⟨S.lower_lt_value p, hpq.trans (S.value_lt_upper q)⟩
  have hq : f q ∈ Ioo (S.lower p) (S.upper q) :=
    ⟨(S.lower_lt_value p).trans hpq, S.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hkeep, hpgerm, hqgerm, hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV F hF hzero hdesc
      hinj cp cq hcp hcq hp hq hpq hq hp (surgery_pair_band_isolation S p q hconsecutive)
        hnoconnection
  have hinjg : InjOn g (criticalPoints E g) := by
    rw [hcrit]
    exact injOn_of_exchanged_values hinj p.property q.property hgp hgq
      (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels : ∀ x ∈ criticalPoints E g, ∃ c : SignedMorseChart (E := E) g x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    rw [hcrit] at hx
    by_cases hxp : x = p.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cp hpgerm
      exact ⟨c, hc ▸ hcp⟩
    by_cases hxq : x = q.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cq hqgerm
      exact ⟨c, hc ▸ hcq⟩
    obtain ⟨c, hc⟩ := hmodels x hx
    obtain ⟨d, hd⟩ := exists_signed_morse_chart_of_germ_preserving_field c (hothers x hx hxp hxq)
    exact ⟨d, hd ▸ hc⟩
  exact ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers,
    (fun x hx => hdescent x (hcrit ▸ hx)), hnewmodels, hindices,
    nativeMorseCount_eq_of_preserved_indices hcrit hindices, hkeep⟩

theorem exists_flow_preserving_value_exchange
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels : ∀ x ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hnoconnection : ∀ x, ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => F t x) atTop (𝓝 p.val))) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ InjOn g (criticalPoints E g) ∧
      g p = f q ∧ g q = f p ∧
      (∀ x ∈ criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f) ∧
      (∀ x, x ∉ criticalPoints E g → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
      (∀ x ∈ criticalPoints E g, ∃ c : SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
      (∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
      ∀ k, nativeMorseCount E g k = nativeMorseCount E f k := by
  obtain ⟨S⟩ := nonempty_surgeryWindows hf hm hinj
  obtain ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hdescg, hmodelsg, hindices, hcounts, _⟩ :=
    exists_flow_preserving_value_exchange_in_windows S hf hm hinj hV F hF hzero hdesc
      hmodels p q hpq hconsecutive hnoconnection
  exact ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hdescg, hmodelsg, hindices, hcounts⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
