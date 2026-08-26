/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-! # The finite B1 divisibility predicate for Erdős 822 -/

namespace Erdos822

/-- Every small prime power one step beyond its exponent in `m` already
divides `φ(m)`.  This is the precise local interface used to preserve the
smooth part of `m + φ(m)` after adjoining an outer prime. -/
def SmoothTotientPreserving (m y : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ y →
    ∀ a : ℕ, a ≤ m.factorization p + 1 → p ^ a ∣ Nat.totient m

end Erdos822
