/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.ShiftedCoefficient

/-! # The reduced totient determinant -/

namespace Erdos822

/-- Absolute totient difference after dividing by the common shifted
coefficient gcd. -/
def reducedTotientDet (m m' : ℕ) : ℕ :=
  ((Nat.totient m : ℤ) - Nat.totient m').natAbs /
    shiftedCoefficientGcd m m'

end Erdos822
