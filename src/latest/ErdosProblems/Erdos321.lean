/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 321.
https://www.erdosproblems.com/forum/thread/321

Informal authors:
- Sandro Bettin
- Loïc Grenié
- Giuseppe Molteni
- Carlo Sanna
- GPT-5.6 Sol

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos321.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/321.lean
-/
import ErdosProblems.Erdos321.FinalAsymptotic

/-!
# Erdős Problem 321

For `N : ℕ`, `R N` is the largest cardinality of a set
`A ⊆ Finset.Icc 1 N` for which the rational reciprocal-sum map is injective
on `A.powerset`.

The theorem below resolves the problem at the terminal iterated-logarithm
depth.  If `d` is the last depth for which the logarithmic tower starting at
`log (log n)` stays above a fixed constant, then `R n` is bounded above and
below by positive constant multiples of

`n / log n * ∏ j ∈ Finset.Icc 3 (d + 2), log^[j] n`.
-/

namespace Erdos321

/-- The extremal function in the notation of the formal-conjectures
statement.  `extremalSize` is its finite-maximum implementation. -/
noncomputable def R (N : ℕ) : ℕ :=
  extremalSize N

theorem R_eq_extremalSize (N : ℕ) : R N = extremalSize N :=
  rfl

/-- Resolution of Erdős Problem 321. -/
theorem erdos_321 :
    ∃ N₀ : ℕ, ∃ B c C : ℝ,
      3 ≤ N₀ ∧ 192 ≤ B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ n, N₀ ≤ n → ∃ d : ℕ,
        d ≤ n ∧ IsTerminalLogDepth B n d ∧
          c * terminalReciprocalScale n d ≤ (R n : ℝ) ∧
          (R n : ℝ) ≤ C * terminalReciprocalScale n d := by
  simpa [R] using erdos321_asymptotic

#print axioms erdos_321

end Erdos321
