/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 746.
https://www.erdosproblems.com/forum/thread/746

Informal authors:
- János Komlós
- Endre Szemerédi

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos746.md
-/
import ErdosProblems.Erdos746.ExpansionProbability
import ErdosProblems.Erdos746.SprinklingThreshold

/-!
# Erdős Problem 746

The expansion estimate supplies a good lower-density prefix with probability
tending to one.  The finite conditioned sprinkling estimate then promotes
that prefix to a Hamiltonian graph at the rounded target threshold.  Finally,
monotonicity transfers the threshold result to every eventually admissible
edge-count sequence above `(1 / 2 + ε) n log n`.
-/

namespace Erdos746

/-- Almost surely, every uniform random graph sequence with eventually at
least `(1 / 2 + ε) n log n` edges is Hamiltonian. -/
theorem erdos_746 : (∀ ε : ℝ, 0 < ε → ∀ m : ℕ → ℕ,
  (∀ᶠ n : ℕ in Filter.atTop,
    (1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ) ≤ (m n : ℝ)) →
  (∀ᶠ n : ℕ in Filter.atTop, m n ≤ n.choose 2) →
  Filter.Tendsto (fun n ↦ Erdos746.hamiltonianProbability n (m n)) Filter.atTop (nhds 1)) := by
  apply erdos746Statement_of_auxiliaryMargin_finite
  · intro ε hε
    change Filter.Tendsto
      (fun n : ℕ ↦ binomialGraphPropertyFailure n
        (clippedEdgeProbability (auxiliaryMargin ε / 2) n)
        (fun G ↦ G.IsTwoExpanderUpTo (n / 4)))
      Filter.atTop (nhds 0)
    exact ExpansionProbability.tendsto_binomial_twoExpanderFailure_zero
      (auxiliaryMargin_pos hε)
  · intro ε hε n hn hnBaseTarget hnTargetCount
    exact
      thresholdFailureProbability_le_base_add_adaptiveSprinklingError
        hn hnBaseTarget hnTargetCount

end Erdos746

#print axioms Erdos746.erdos_746
