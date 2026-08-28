import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenMorseCancellation
import Wikipedia.HopfProblem.DegreeCollapseNativeIndexDisorder
import Wikipedia.HopfProblem.DegreeCollapseBoundedPrescribedFlowWindows

/-!
# Actual positive critical-value exchange fixes the original nonpositive half

Construct adapted windows avoiding zero and apply the proved native
exchange of adjacent nonincreasing indices. The two exchanged values
remain strictly inside that positive band. The compact-band theorem
retains the signs and zero set, so the result is an excellent Morse
presentation of the same original state. Every nonpositive point keeps
its entire old function germ, and the original critical set and all
native indices are unchanged.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_positive_index_exchange
    (p q : criticalPoints (Vector 7) P.function)
    (hpositive : 0 < P.function p) (hpq : P.function p < P.function q)
    (hconsecutive : ∀ r : criticalPoints (Vector 7) P.function,
      ¬(P.function p < P.function r ∧ P.function r < P.function q))
    (hle : nativeMorseIndex (Vector 7) P.function q ≤ nativeMorseIndex (Vector 7) P.function p) :
    ∃ Q : S.ExcellentMorsePresentation,
      criticalPoints (Vector 7) Q.function = criticalPoints (Vector 7) P.function ∧
      Q.function p = P.function q ∧ Q.function q = P.function p ∧
      (∀ z, S.time z ≤ 0 → Q.function =ᶠ[𝓝 z] P.function) ∧
      (∀ z ∈ criticalPoints (Vector 7) P.function, z ≠ p.val → z ≠ q.val →
        Q.function =ᶠ[𝓝 z] P.function) ∧
      (∀ z ∈ criticalPoints (Vector 7) P.function,
        nativeMorseIndex (Vector 7) Q.function z = nativeMorseIndex (Vector 7) P.function z) ∧
      ∀ k, nativeMorseCount (Vector 7) Q.function k = nativeMorseCount (Vector 7) P.function k := by
  obtain ⟨A⟩ := nonempty_adaptedSurgeryWindows P.smooth P.morse P.distinct
  obtain ⟨T, _, _, _, _, hTpositive⟩ := A.exists_same_flow_windows_avoiding_level P.smooth P.morse
    (RegularTimeMorse.regular_zero_not_critical P.regular)
  have hlow : 0 < T.toSurgeryWindows.lower p := hTpositive p hpositive
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hkeep, hothers, hinj, _, hindices, hcounts⟩ :=
    T.exchange_nonincreasing_native_indices P.smooth P.morse p q hpq hconsecutive hle
  have hvalues (x : S.Space)
      (hx : P.function x ∈ Icc (T.toSurgeryWindows.lower p) (T.toSurgeryWindows.upper q))
      (hxc : x ∈ criticalPoints (Vector 7) g) :
      g x ∈ Ioo (T.toSurgeryWindows.lower p) (T.toSurgeryWindows.upper q) := by
    have hxf : x ∈ criticalPoints (Vector 7) P.function := hcrit ▸ hxc
    rcases surgery_pair_band_isolation T.toSurgeryWindows p q hconsecutive x hxf hx with he | he
    · rw [he, hgp]
      exact ⟨(T.toSurgeryWindows.lower_lt_value p).trans hpq,
        T.toSurgeryWindows.value_lt_upper q⟩
    · rw [he, hgq]
      exact ⟨T.toSurgeryWindows.lower_lt_value p,
        hpq.trans (T.toSurgeryWindows.value_lt_upper q)⟩
  let Q := P.replacePositiveBandWithCriticalValues ⟨g, hg.continuous⟩ hg hmg hinj
    hlow.le hkeep hvalues
  refine ⟨Q, hcrit, hgp, hgq, ?_, hothers, hindices, hcounts⟩
  intro z hz
  apply hkeep z
  intro hband
  have hpos : 0 < P.function z := hlow.trans hband.1
  exact (not_lt_of_ge hz) ((P.positive_iff z).mp hpos)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
