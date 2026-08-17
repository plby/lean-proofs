/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the resolution of Erdős Problem 285.

The theorem is the logical payload of the Google DeepMind Formal Conjectures
statement.

Informal author:
- Greg Martin

Formalization:
- OpenAI Codex

Primary references:
- https://doi.org/10.4064/aa-95-3-231-260
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/285.lean
-/
import ErdosProblems.Erdos285.MartinUpperFinal
import ErdosProblems.Erdos285.RatioBridge
import ErdosProblems.Erdos285.Erdos285Packaging

open Filter
open scoped BigOperators Topology Real

namespace Erdos285

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Erdős Problem 285: the least possible largest denominator in a
`k + 1`-term representation of `1` by distinct unit fractions is asymptotic
to `e / (e - 1) * (k + 1)`. -/
theorem erdos_285 :
    True ↔ ∀ᵉ (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)),
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S,
        f k = (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) := by
  apply erdos_285_of_uniform_ratio
  intro f S hS h
  exact uniform_ratio_of_eventually_upperWitness f S hS h
    MartinUpperFinal.martinCutoff
    MartinUpperFinal.eventually_martinUpperWitness
    MartinUpperFinal.martinCutoff_ratio_tendsto

end


end Erdos285

#print axioms Erdos285.erdos_285
