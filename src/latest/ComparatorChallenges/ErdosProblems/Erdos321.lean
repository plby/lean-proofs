/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

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

def reciprocalSubsetSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, ((n : ℚ)⁻¹)

def Valid (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powerset, ∀ T ∈ A.powerset,
    reciprocalSubsetSum S = reciprocalSubsetSum T → S = T

noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter Valid

noncomputable def extremalSize (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

noncomputable def realIteratedLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (realIteratedLog k x)

noncomputable def iteratedLogTailProduct : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x => Real.log x * iteratedLogTailProduct k (Real.log x)

def LogTowerAbove (B : ℝ) (k : ℕ) (x : ℝ) : Prop :=
  ∀ j ≤ k, B ≤ realIteratedLog j x

def IsTerminalLogDepth (B : ℝ) (n d : ℕ) : Prop :=
  LogTowerAbove B d (Real.log (Real.log (n : ℝ))) ∧
    realIteratedLog (d + 1) (Real.log (Real.log (n : ℝ))) < B

noncomputable def terminalReciprocalScale (n d : ℕ) : ℝ :=
  (n : ℝ) / Real.log n *
    iteratedLogTailProduct d (Real.log (Real.log (n : ℝ)))

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
