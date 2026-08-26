/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.StructuredInputs

/-! # Fixed-cofactor outer collision pairs -/

namespace Erdos822

/-- Pairs of outer primes producing the same shifted-totient value for fixed
cofactors. -/
def outerCollisionPairs (x m m' : ℕ) : Finset (ℕ × ℕ) :=
  ((outerPrimes x m).product (outerPrimes x m')).filter fun z ↦
    shiftedTotient (m * z.1) = shiftedTotient (m' * z.2)

@[simp]
theorem mem_outerCollisionPairs_iff
    {x m m' p p' : ℕ} :
    (p, p') ∈ outerCollisionPairs x m m' ↔
      p ∈ outerPrimes x m ∧ p' ∈ outerPrimes x m' ∧
        shiftedTotient (m * p) = shiftedTotient (m' * p') := by
  simp [outerCollisionPairs, and_assoc]

end Erdos822
