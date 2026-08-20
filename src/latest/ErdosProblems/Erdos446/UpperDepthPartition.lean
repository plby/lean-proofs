/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDepthComparison
import ErdosProblems.Erdos446.UpperBlockPartition

/-!
# Erdős Problem 446: inserting the terminal depth in the upper partition

This is the bookkeeping bridge from the actual cutoff `2*y` to the generic
`blockPool M K` partition.  The final selected block may be only partially
used, so the upper argument retains every block through the next endpoint.
-/

namespace Erdos446

open Finset

theorem small_union_upperBlocks_eq_primesUpTo_endpoint
    {M y : ℕ} (hy : fordConstructionScale M 1 ≤ y) :
    smallPrimePool M ∪ blockPool M (upperPrimeBlockCount M y) =
      primesUpTo (blockEndpoint (upperPrimeBlockDepth y + 1)) := by
  rw [← smoothSupport_eq_small_union_blocks M (upperPrimeBlockCount M y),
    upperPrimeBlockCount_terminal_endpoint hy]

/-- Every prime that can divide an integer supported below `2*y` occurs in
the small-prime part or one of the retained upper blocks. -/
theorem primesUpTo_two_mul_subset_small_union_upperBlocks
    {M y : ℕ} (hy : fordConstructionScale M 1 ≤ y) :
    primesUpTo (2 * y) ⊆
      smallPrimePool M ∪ blockPool M (upperPrimeBlockCount M y) := by
  rw [small_union_upperBlocks_eq_primesUpTo_endpoint hy,
    primesUpTo_eq_primesLE, primesUpTo_eq_primesLE]
  apply Nat.primesLE_mono
  exact (lt_blockEndpoint_upperPrimeBlockDepth_succ (by
    have := (depth_lt_fordConstructionScale M 1).trans_le hy
    omega)).le

end Erdos446
