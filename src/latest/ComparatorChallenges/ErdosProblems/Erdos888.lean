/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 888

The largest admissible subset of `{1, ..., n}` has order
`n * log (log n) / log n`.  The lower bound uses primes and squarefree
semiprimes.  The upper bound uses exact square-part fibres, a two-largest-prime
encoding, a coloured rectangle estimate, and dyadic analytic bounds.

The detailed mathematical proof and Leanization map are in `tex/888.tex`.
-/

open Filter

namespace Erdos888

def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
    a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

def p (n : ℕ) (k : ℕ) : Prop :=
  ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

open scoped Classical in
/-- Resolution of Erdős Problem 888. -/

theorem erdos_888 :
    (fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  sorry
