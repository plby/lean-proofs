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

theorem erdos_321 :
    ∃ N₀ : ℕ, ∃ B c C : ℝ,
      3 ≤ N₀ ∧ 192 ≤ B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ n, N₀ ≤ n → ∃ d : ℕ,
        d ≤ n ∧ IsTerminalLogDepth B n d ∧
          c * terminalReciprocalScale n d ≤ (R n : ℝ) ∧
          (R n : ℝ) ≤ C * terminalReciprocalScale n d := by
  sorry

