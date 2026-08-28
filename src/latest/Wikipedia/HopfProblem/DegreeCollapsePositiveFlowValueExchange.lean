import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenPositiveExchange
import Wikipedia.HopfProblem.DegreeCollapseFlowPreservingValueExchange

/-!
# Positive value exchange retaining the original field, flow, and zero boundary

Use windows avoiding zero in the strengthened native no-connection
exchange. The full exterior germ and the exchanged critical values keep
the result in the original state's excellent presentations. All critical
model fields and the same complete flow are retained for further moves.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_positive_flow_preserving_exchange
    {V : (x : S.Space) → TangentSpace (𝓡 7) x}
    (hV : ContMDiff (𝓡 7) (𝓡 7).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 7) S.Space)))
    (F : Flow ℝ S.Space) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints (Vector 7) P.function, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints (Vector 7) P.function →
      mvfderiv (𝓡 7) P.function x (V x) < 0)
    (hmodels : ∀ x ∈ criticalPoints (Vector 7) P.function,
      ∃ c : SignedMorseChart (E := Vector 7) P.function x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : criticalPoints (Vector 7) P.function)
    (hpositive : 0 < P.function p) (hpq : P.function p < P.function q)
    (hconsecutive : ∀ r : criticalPoints (Vector 7) P.function,
      ¬(P.function p < P.function r ∧ P.function r < P.function q))
    (hnoconnection : ∀ x, ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => F t x) atTop (𝓝 p.val))) :
    ∃ Q : S.ExcellentMorsePresentation,
      criticalPoints (Vector 7) Q.function = criticalPoints (Vector 7) P.function ∧
      Q.function p = P.function q ∧ Q.function q = P.function p ∧
      (∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function) ∧
      (∀ x ∈ criticalPoints (Vector 7) P.function, x ≠ p.val → x ≠ q.val →
        Q.function =ᶠ[𝓝 x] P.function) ∧
      (∀ x, x ∉ criticalPoints (Vector 7) Q.function →
        mvfderiv (𝓡 7) Q.function x (V x) < 0) ∧
      (∀ x ∈ criticalPoints (Vector 7) Q.function,
        ∃ c : SignedMorseChart (E := Vector 7) Q.function x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
      (∀ x ∈ criticalPoints (Vector 7) P.function,
        nativeMorseIndex (Vector 7) Q.function x = nativeMorseIndex (Vector 7) P.function x) ∧
      ∀ k, nativeMorseCount (Vector 7) Q.function k = nativeMorseCount (Vector 7) P.function k := by
  obtain ⟨A⟩ := nonempty_adaptedSurgeryWindows P.smooth P.morse P.distinct
  obtain ⟨T, _, _, _, _, hTpositive⟩ := A.exists_same_flow_windows_avoiding_level P.smooth P.morse
    (RegularTimeMorse.regular_zero_not_critical P.regular)
  have hlow : 0 < T.toSurgeryWindows.lower p := hTpositive p hpositive
  obtain ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, hothers, hdescg, hmodelsg, hindices,
    hcounts, hkeep⟩ := exists_flow_preserving_value_exchange_in_windows T.toSurgeryWindows
      P.smooth P.morse P.distinct hV F hF hzero hdesc hmodels p q hpq hconsecutive hnoconnection
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
  refine ⟨Q, hcrit, hgp, hgq, ?_, hothers, hdescg, hmodelsg, hindices, hcounts⟩
  intro x hx
  apply hkeep x
  intro hband
  exact (not_lt_of_ge hx) ((P.positive_iff x).mp (hlow.trans hband.1))

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
