import Wikipedia.HopfProblem.DegreeCollapseSublevelFlowWindows
import Wikipedia.HopfProblem.DegreeCollapseFlowPreservingValueExchange
import Wikipedia.HopfProblem.DegreeCollapseRegularBandReplacement

/-!
# A flow-preserving exchange strictly below the original cut

Both exchanged critical values lie below the cut. Small native windows
and compact-band control retain the entire germ on the closed upper
region and the literal strict sublevel, as well as the same field, flow,
critical models, indices, and all indexed counts.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem exists_flow_preserving_value_exchange_below_cut
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
    (p q : criticalPoints E f) (hpq : f p < f q) {a : ℝ} (hqa : f q < a)
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
      (∀ x, a ≤ f x → g =ᶠ[𝓝 x] f) ∧
      ∀ x, g x < a ↔ f x < a := by
  obtain ⟨A⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  obtain ⟨T, _, _, _, hcut⟩ := A.exists_same_flow_windows_below_cut hf hm a
  obtain ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hdescg, hmodelsg,
      hindices, hcounts, hkeep⟩ := exists_flow_preserving_value_exchange_in_windows
    T.toSurgeryWindows hf hm hinj hV F hF hzero hdesc hmodels p q hpq
      hconsecutive hnoconnection
  have hvalues (x : M)
      (hx : f x ∈ Icc (T.toSurgeryWindows.lower p) (T.toSurgeryWindows.upper q))
      (hxc : x ∈ criticalPoints E g) :
      g x ∈ Ioo (T.toSurgeryWindows.lower p) (T.toSurgeryWindows.upper q) := by
    rcases surgery_pair_band_isolation T.toSurgeryWindows p q hconsecutive
      x (hcrit ▸ hxc) hx with he | he
    · rw [he, hgp]
      exact ⟨(T.toSurgeryWindows.lower_lt_value p).trans hpq,
        T.toSurgeryWindows.value_lt_upper q⟩
    · rw [he, hgq]
      exact ⟨T.toSurgeryWindows.lower_lt_value p,
        hpq.trans (T.toSurgeryWindows.value_lt_upper q)⟩
  refine ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hdescg, hmodelsg,
    hindices, hcounts, ?_, ?_⟩
  · intro x hx
    apply hkeep x
    intro hband
    exact (not_lt_of_ge hx) (hband.2.trans (hcut q hqa))
  · intro x
    by_cases hx : f x ∈ Ioo (T.toSurgeryWindows.lower p) (T.toSurgeryWindows.upper q)
    · have hgx := RegularBandReplacement.mem_open_band_of_critical_values hf hg
        (fun y hy => (hkeep y hy).self_of_nhds) hvalues hx
      exact iff_of_true (hgx.2.trans (hcut q hqa)) (hx.2.trans (hcut q hqa))
    · rw [(hkeep x hx).self_of_nhds]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
