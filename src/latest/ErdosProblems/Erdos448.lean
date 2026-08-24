/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 448.
https://www.erdosproblems.com/forum/thread/448

Informal authors:
- Paul Erdős
- Gérald Tenenbaum

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos448.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/448.lean
-/
/-
Erdős Problem 448.

The mathematical proof and the endpoint-convention comparison with the
Erdős--Tenenbaum theorem are documented in tex/448.tex.
-/

import ErdosProblems.Erdos448.Final448Assembly

namespace Erdos448

/-- Erdős Problem 448 has a negative answer: for some positive threshold,
the exceptional set has upper density strictly smaller than one. -/
theorem not_erdos_448 :
    ¬ ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (tauPlus n : ℝ) <
        ε * (n.divisors.card : ℝ)}.HasDensity 1 :=
  Erdos448FinalAssembly.erdos_448_of_naturalGrid_linear_moment
    Erdos448Prop3Assembly.naturalGridSelectedPair_eventually_linear_all_K

end Erdos448

#print axioms Erdos448.not_erdos_448

alias _root_.Erdos448.erdos_448 := _root_.Erdos448.not_erdos_448
