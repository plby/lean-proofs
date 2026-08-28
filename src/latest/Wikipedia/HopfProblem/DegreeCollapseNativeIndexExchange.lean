import Wikipedia.HopfProblem.DegreeCollapseEmptyCoreConnections
import Wikipedia.HopfProblem.DegreeCollapseNoConnectionMorseRearrangement
import Wikipedia.HopfProblem.DegreeCollapseMorseValueExchange

/-!
# Constructed exchange of every adjacent nonincreasing native-index pair

Ambient avoidance, including the empty-core cases, removes the selected
connections. The unchanged critical field germs then construct the global
critical-value exchange. Its critical set and intrinsic indices are exactly
preserved, every indexed count is unchanged, and a new excellent compatible
surgery system is constructed. There is no signed-count or contraction
hypothesis in this index-ordering move.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exchange_nonincreasing_native_indices
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle : nativeMorseIndex E f q ≤ nativeMorseIndex E f p) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ g p = f q ∧ g q = f p ∧
      (∀ z, f z ∉ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
        g =ᶠ[𝓝 z] f) ∧
      (∀ z ∈ criticalPoints E f, z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
      InjOn g (criticalPoints E g) ∧ Nonempty (AdaptedSurgeryWindows E g) ∧
      (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
      ∀ k, nativeMorseCount E g k = nativeMorseCount E f k := by
  have hle' : Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
      Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rwa [nativeMorseIndex_eq_chart (S.data q).chart, nativeMorseIndex_eq_chart (S.data p).chart] at hle
  obtain ⟨V, G, hV, hG, hzeros, hneg, hgerms, hnoconnection⟩ :=
    S.remove_connections_of_nonincreasing_indices hf p q hpq hconsecutive hle'
  have hpgerm : ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p p.property, S.critical_model_germ p] with y hy hmodel
    exact hy.trans hmodel
  have hqgerm : ∀ᶠ y in 𝓝 q.val, V y = (S.data q).chart.descentField y := by
    filter_upwards [hgerms q q.property, S.critical_model_germ q] with y hy hmodel
    exact hy.trans hmodel
  have hpband : f p ∈ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, -, hexterior, -, -, hothers, hindices⟩ :=
    MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV G hG hzeros hneg
      S.distinct (S.data p).chart (S.data q).chart hpgerm hqgerm hpband hqband hpq hqband hpband
      (surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hnoconnection
  obtain ⟨hinj, hnew⟩ := adapted_surgery_system_after_value_exchange S hg hmg
    p.property q.property hcrit hgp hgq hothers
  exact ⟨g, hg, hmg, hcrit, hgp, hgq, hexterior, hothers, hinj, hnew, hindices,
    nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
