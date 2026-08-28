import Wikipedia.SmoothSixDPoincare.MorseSurgeryWindows

/-!
# The actual isolated pair band for consecutive surgery windows

The outer band contains precisely the selected critical pair, and every
closed band strictly inside their value gap is regular. Both facts follow
from the constructed windows and consecutiveness in the original critical set.
-/

noncomputable section

open Set Function
open scoped ContDiff Topology Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

theorem surgery_pair_band_isolation (S : SurgeryWindows E f)
    (p q : criticalPoints E f)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ z ∈ criticalPoints E f, f z ∈ Icc (S.lower p) (S.upper q) →
      z = p.val ∨ z = q.val := by
  intro z hz hband
  by_cases hzp : f z ≤ f p
  · exact Or.inl (S.isolated p z hz ⟨hband.1, hzp.trans (S.value_lt_upper p).le⟩)
  by_cases hqz : f q ≤ f z
  · exact Or.inr (S.isolated q z hz ⟨(S.lower_lt_value q).le.trans hqz, hband.2⟩)
  exact (hconsecutive ⟨z, hz⟩ ⟨lt_of_not_ge hzp, lt_of_not_ge hqz⟩).elim

theorem surgery_pair_inner_band_regular (S : SurgeryWindows E f)
    (p q : criticalPoints E f)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    {a b : ℝ} (ha : f p < a) (hb : b < f q) :
    ∀ z, f z ∈ Icc a b → z ∉ criticalPoints E f := by
  intro z hz hcrit
  exact hconsecutive ⟨z, hcrit⟩ ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
