/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 485.
https://www.erdosproblems.com/forum/thread/485

Informal authors:
- Andrzej Schinzel

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos485.md
-/
import ErdosProblems.Erdos485.Schinzel

/-!
# Erdős Problem 485

For a rational polynomial `P`, `termCount P` is the cardinality of its
coefficient support.  The function `f k` is the attained minimum of
`termCount (P ^ 2)` over all rational polynomials having exactly `k` nonzero
terms.  Schinzel's support estimate, proved in the imported development,
implies that this minimum tends to infinity.

The quantitative theorem `schinzel_support_bound` formalizes the square case
of Schinzel's 1987 estimate.  The theorem below is the affirmative resolution
of the question asked in Problem 485.
-/

namespace Erdos485

open Filter

/-- Erdős Problem 485: the minimum number of terms in the square of a
rational polynomial with exactly `k` nonzero terms tends to infinity as
`k → ∞`. -/
theorem erdos_485 : Tendsto f atTop atTop :=
  erdos_485_from_schinzel

#print axioms Erdos485.erdos_485

end Erdos485
