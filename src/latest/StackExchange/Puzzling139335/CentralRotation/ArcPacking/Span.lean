import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-!
# A uniform parameter-span bound from a diameter bound

Uniform continuity of a compact-interval curve is sufficient.  In particular,
the curve is not assumed to be rectifiable or Lipschitz.
-/

open Set

namespace Puzzling139335.CentralRotation.ArcPacking

/-- Subinterval images whose diameter is at least a fixed positive value have
a uniformly positive parameter span. Injectivity is not needed here. -/
theorem exists_uniform_span_lower_bound {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {L U ε : ℝ} (hf : ContinuousOn f (Icc L U)) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ a ∈ Icc L U, ∀ b ∈ Icc L U, a ≤ b →
      ε ≤ Metric.diam (f '' Icc a b) → η ≤ b - a := by
  obtain ⟨η, hη, hsmall⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) (half_pos hε)
  refine ⟨η, hη, ?_⟩
  intro a ha b hb hab hdiam
  by_contra hspan
  have hspan' : b - a < η := lt_of_not_ge hspan
  have hbound : Metric.diam (f '' Icc a b) ≤ ε / 2 := by
    apply Metric.diam_le_of_forall_dist_le (half_pos hε).le
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    have hsI : s ∈ Icc L U := ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
    have htI : t ∈ Icc L U := ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
    have hdist : dist s t < η := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    exact (hsmall s hsI t htI hdist).le
  linarith

end Puzzling139335.CentralRotation.ArcPacking
