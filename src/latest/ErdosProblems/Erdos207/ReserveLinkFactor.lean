/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveAwareSimultaneousMasterLaw

/-!
# Scalar factorization for the reserve-supported link stage

The two reserve spokes and one sparsified-link coordinate contributed by
each new matching triangle combine into one per-triangle factor.  These
identities isolate that factor before the eventual parameter inequalities
are applied.
-/

namespace Erdos207

open scoped NNReal

lemma linkReserveFactor_pow (alpha r : ℝ≥0) (t : ℕ) :
    alpha ^ t * r ^ (2 * t) = (alpha * r ^ 2) ^ t := by
  rw [pow_mul]
  exact (mul_pow alpha (r ^ 2) t).symm

lemma linkReserveConstantFactor_pow (alpha C r : ℝ≥0) (t : ℕ) :
    alpha ^ t * C ^ (2 * t) * r ^ (2 * t) =
      (alpha * C ^ 2 * r ^ 2) ^ t := by
  rw [pow_mul, pow_mul]
  rw [mul_pow, mul_pow]

/-- Exact split of a reserve-aware powerset term into its main product and
additive-error contributions. -/
lemma linkReservePartitionTerm_factor
    (alpha C r x y b : ℝ≥0) (m t : ℕ) :
    alpha ^ t *
        (C ^ (m + 2 * t) * (x * r ^ (2 * t) * y + b)) =
      C ^ m *
        (x * y * (alpha * C ^ 2 * r ^ 2) ^ t +
          b * (alpha * C ^ 2) ^ t) := by
  rw [pow_add, pow_mul, pow_mul]
  rw [mul_pow, mul_pow]
  ring

end Erdos207
