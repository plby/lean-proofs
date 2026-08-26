/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.Core

/-! # The common shifted-totient coefficient -/

namespace Erdos822

/-- The common shifted coefficient before primitive reduction. -/
def shiftedCoefficientGcd (m m' : ℕ) : ℕ :=
  Nat.gcd (shiftedTotient m) (shiftedTotient m')

theorem shiftedCoefficientGcd_comm (m m' : ℕ) :
    shiftedCoefficientGcd m m' = shiftedCoefficientGcd m' m := by
  simp [shiftedCoefficientGcd, Nat.gcd_comm]

end Erdos822
