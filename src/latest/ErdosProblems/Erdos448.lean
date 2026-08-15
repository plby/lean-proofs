/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 448.

The mathematical proof and the endpoint-convention comparison with the
Erdős--Tenenbaum theorem are documented in tex/448.tex.
-/

import ErdosProblems.Erdos448.Final448Assembly

namespace Erdos448

/-- Erdős Problem 448 has a negative answer: for some positive threshold,
the exceptional set has upper density strictly smaller than one. -/
theorem erdos_448 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (tauPlus n : ℝ) <
        ε * (n.divisors.card : ℝ)}.HasDensity 1 :=
  Erdos448FinalAssembly.erdos_448_of_naturalGrid_linear_moment
    Erdos448Prop3Assembly.naturalGridSelectedPair_eventually_linear_all_K

end Erdos448

#print axioms Erdos448.erdos_448
