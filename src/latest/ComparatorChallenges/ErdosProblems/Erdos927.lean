/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license.
Definitions adapted for this repository from the original formalization.
-/
import Mathlib

namespace Erdos927

/-- A finset `s` is a maximal clique of `G` if `s` is a clique and no proper superset
  of `s` (as a finset) is a clique. -/
def IsMaximalClique {α : Type*} (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsClique (↑s : Set α) ∧ ∀ t : Finset α, G.IsClique (↑t : Set α) → s ⊆ t → t = s

/-- The set of sizes of maximal cliques in a graph. -/
noncomputable def maximalCliqueSizes {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : Finset ℕ := by
  classical
  exact ((Finset.univ (α := Finset α)).filter (fun s => IsMaximalClique G s)).image Finset.card

/-- `g n` is the maximum number of different sizes of maximal cliques
  that can occur in a graph on `n` vertices. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Finset.sup (Finset.univ (α := SimpleGraph (Fin n)))
    (fun G => (maximalCliqueSizes G).card)

/-- The iterated logarithm (log-star) function. `logStar n` is the number of times
  one must take `Nat.log 2` before reaching a value ≤ 1. -/
def logStar : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => logStar (Nat.log 2 (n + 2)) + 1
termination_by n => n
decreasing_by
  simp_wf
  have : Nat.log 2 (n + 2) < n + 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    exact Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2)
  omega

theorem not_erdos_927 :
    ¬ (∃ C n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → g n + Nat.log 2 n + logStar n ≤ n + C) := by
  sorry

end Erdos927
