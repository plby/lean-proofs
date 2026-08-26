import ErdosProblems.Erdos486.Proof

/-!
Lean 4.33.0 port of Shouqiao Wang's formalization of the negative answer to
Erdős Problem 486. Source, attribution, and verification are in Erdos486/README.md.
-/

namespace Erdos486

/-- One fixed infinite system has distinct lower and upper logarithmic densities. -/
theorem erdos_486_quantitative :
    ∃ (A : Set ℕ), A.Infinite ∧ 0 ∉ A ∧
      ∃ X : (n : A) → Set (ZMod (n : ℕ)),
        (¬ ∃ d : ℝ, Filter.Tendsto (logAverage (survivors A X)) Filter.atTop (nhds d)) ∧
        Filter.liminf (logAverage (survivors A X)) Filter.atTop ≤ (177 : ℝ) / 200 ∧
        (49 : ℝ) / 50 ≤ Filter.limsup (logAverage (survivors A X)) Filter.atTop := by
  exact erdos486_quantitativeCounterexample

/-- Arbitrary delayed congruence systems need not have logarithmic density. -/
theorem not_erdos_486 :
    ¬ ∀ (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))), 0 ∉ A →
      ∃ d : ℝ, Filter.Tendsto (logAverage (survivors A X)) Filter.atTop (nhds d) := by
  exact erdos486_negative

end Erdos486

#print axioms Erdos486.erdos_486_quantitative
#print axioms Erdos486.not_erdos_486
