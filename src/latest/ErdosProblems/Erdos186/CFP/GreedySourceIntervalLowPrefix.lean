/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyLowPrefix
import ErdosProblems.Erdos186.CFP.HDimension

/-!
# Low greedy prefixes for sources in an integer interval

The minimum defining the CFP threshold may be evaluated at the original
source itself.  If the anchored source lies in `[0,n-1]`, its `2^h`-fold
sumset has at most `2^h*n` elements.  Combining this elementary interval
bound with `GreedyLowPrefix` gives the explicit logarithmic prefix estimate
used by the outer random-colour selector.
-/

namespace Erdos186.CFP.Greedy

open GrowthLemmas

/-- The positive level-`h` source threshold is at most the elementary
interval cardinality `2^h*n+1`. -/
theorem positiveDyadicThreshold_le_sourceInterval
    {S : Finset ℤ} {budget h n : ℕ}
    (hn : 0 < n)
    (hS : insert 0 S ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) :
    positiveDyadicThreshold S budget h ≤ 2 ^ h * n + 1 := by
  have hminimum :
      minimumMultifoldCardinality S budget (2 ^ h) ≤
        (multifoldSumset (2 ^ h) (insert 0 S)).card := by
    exact minimumMultifoldCardinality_le
      (B := S) Finset.Subset.rfl (by omega)
  have hinterval :
      (multifoldSumset (2 ^ h) (insert 0 S)).card ≤ 2 ^ h * n :=
    HDimension.card_multifoldSumset_le_mul_of_subset_Icc
      (by positivity) hn hS
  simp only [positiveDyadicThreshold, dyadicThreshold, foldThreshold]
  omega

/-- Explicit interval form of the low-prefix bound. -/
theorem dyadicBinStart_le_sourceIntervalLog
    {S : Finset ℤ} {budget cap low n : ℕ}
    (hn : 0 < n)
    (hS : insert 0 S ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hcapCard : cap ≤ S.card)
    (hcapBudget : cap ≤ budget) :
    dyadicBinStart S budget cap low ≤
      2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) := by
  have hprefix := dyadicBinStart_le_dyadicBlock_mul_log
    (A := S) (deletionBudget := budget) (steps := cap) (h := low)
    hcapCard hcapBudget
  have hthreshold := positiveDyadicThreshold_le_sourceInterval
    (S := S) (budget := budget) (h := low) hn hS
  have hlog :
      Nat.log 2 (positiveDyadicThreshold S budget low) ≤
        Nat.log 2 (2 ^ low * n + 1) :=
    Nat.log_mono_right hthreshold
  exact hprefix.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1))

end Erdos186.CFP.Greedy

#print axioms
  Erdos186.CFP.Greedy.dyadicBinStart_le_sourceIntervalLog
