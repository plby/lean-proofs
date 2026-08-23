/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 851.
https://www.erdosproblems.com/forum/thread/851

Informal authors:
- Lisa Price
- GPT-5.2 Pro

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos851.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/851.lean
-/
import ErdosProblems.Erdos851.UniformBetaEstimates

/-!
# Erdős Problem 851

The source-faithful formulation asks for lower density.  The analytic proof
uses the Price--Tao rough-residual sieve, first and second moments, and the
averaged Romanoff singular-series estimate.  The detailed mathematical proof
and the map from its lemmas to this development are in `tex/851.tex`.
-/

namespace Erdos851

/-- For every positive error below one, integers representable as a power of
two plus a number with boundedly many distinct prime factors have lower
density at least `1 - ε`. -/
theorem erdos_851 (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ∃ r : ℕ, 1 - ε ≤ (TwoPowAddSet r).lowerDensity :=
  erdos_851_of_uniformBetaCardinalEstimates
    uniform_beta_cardinal_estimates ε hε

#print axioms erdos_851

end Erdos851
