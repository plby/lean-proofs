import ErdosProblems.Erdos796.Proof

/-!
Rishikesh Gajjala's version 1.0.0 formalization, developed with GPT-5.6 Sol,
ported from Lean 4.30.0 to 4.33.0. See Erdos796/README.md for provenance.
-/

namespace Erdos796

/-- The second-order constant exists and is less than fifteen. -/
theorem erdos_796_upper :
    ∃ c : ℝ, c < 15 ∧ Filter.Tendsto
      (fun n : ℕ =>
        ((g3 n : ℝ) - (n : ℝ) * Real.log (Real.log n) / Real.log n) /
          ((n : ℝ) / Real.log n))
      Filter.atTop (nhds c) := by
  exact ⟨1 + Mertens.M + Gamma, secondOrderConstant_lt_fifteen, hasSecondOrderConstant⟩

/-- The normalized second-order residual has a finite limit. -/
theorem erdos_796 :
    ∃ c : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        ((g3 n : ℝ) - (n : ℝ) * Real.log (Real.log n) / Real.log n) /
          ((n : ℝ) / Real.log n))
      Filter.atTop (nhds c) := by
  obtain ⟨c, _, hc⟩ := erdos_796_upper
  exact ⟨c, hc⟩

end Erdos796

#print axioms Erdos796.erdos_796_upper
#print axioms Erdos796.erdos_796
