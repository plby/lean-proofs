/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyDyadicRange
import ErdosProblems.Erdos186.CFP.GreedySourceIntervalLowPrefix

/-!
# Source dyadic-range crossing

This module joins the shifted greedy-bin estimate to the exact dyadic
approximation range.  The color level may vary: the sole remaining outer
obligation is the explicit inequality saying that the chosen cap is larger
than its low prefix and the active-bin budget.
-/

namespace Erdos186.CFP

noncomputable section

namespace Greedy

/-- Reaching a threshold at `cap` makes its first crossing, when searched
through `cap + 1`, strict.  This removes the harmless endpoint strictness
from consumers phrased with `dyadicBinStart`.-/
theorem dyadicBinStart_succ_lt_of_threshold_le_card_sums
    {S : Finset ℤ} {deletionBudget cap level : ℕ}
    (hend : positiveDyadicThreshold S deletionBudget level ≤
      (sums S cap).card) :
    dyadicBinStart S deletionBudget (cap + 1) level < cap + 1 := by
  have hle : dyadicBinStart S deletionBudget (cap + 1) level ≤ cap := by
    apply Nat.find_min'
    exact Or.inr hend
  omega

/-- A color reaches its terminal positive threshold whenever the cap is
larger than the low prefix plus the uniform active-bin budget.  Stability
may be stated relative to the fixed minimal boxes of the preprocessing
weak core; it is converted internally to the color's canonical boxes. -/
theorem positiveDyadicThreshold_le_card_sums_of_dyadicRange
    {source W S : Finset ℤ}
    {low high terminal deletionBudget cap D n propernessDenominator : ℕ}
    (hfamily : PreprocessingBilu.DyadicRangeSourceHApproximationFamily
      source low high D 1
        (PreprocessingBilu.preprocessingScaleDen propernessDenominator))
    (hlowTerminal : low < terminal) (hterminalHigh : terminal ≤ high)
    (hSsource : insert 0 S ⊆ source) (hSW : insert 0 S ⊆ W)
    (hzeroS : 0 ∉ S) (hSnonempty : S.Nonempty)
    (hcapCard : cap ≤ S.card) (hcapBudget : cap ≤ deletionBudget)
    (hbudget : deletionBudget < S.card)
    (hstable : Stability.WeaklyStableFor (insert 0 S)
      (Stability.minimalBoxFamily W) deletionBudget D (n ^ 2))
    (hinterval : ∀ z ∈ insert 0 S, 0 ≤ z ∧ z < (n : ℤ))
    (hfoldn : ∀ h, low ≤ h → h < terminal → 2 ^ h ≤ n)
    (hlarge : ∀ h, low ≤ h → h < terminal →
      PreprocessingBilu.preprocessingIndexBound D propernessDenominator ≤
        2 ^ h)
    (hcapLarge :
      dyadicBinStart S deletionBudget cap low +
          16 *
            (2 * (6 * PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ^ D *
              (4 * (4 * PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ^ D) + 1) *
            2 ^ terminal < cap) :
    positiveDyadicThreshold S deletionBudget terminal ≤
      (sums S cap).card := by
  let ratio :=
    2 * (6 * PreprocessingBilu.preprocessingScaleDen
        propernessDenominator) ^ D *
      (4 * (4 * PreprocessingBilu.preprocessingScaleDen
        propernessDenominator) ^ D) + 1
  have hcanonical : Stability.WeaklyStableMinimalFor
      (insert 0 S) deletionBudget D n :=
    weaklyStableMinimalFor_of_fixed_minimalBox hSW hstable
  apply positiveDyadicThreshold_le_card_sums_of_shiftedPrefix_lt
    hlowTerminal hcapCard hcapBudget
  · intro h hlow hterminal
    apply positiveDyadicThreshold_succ_le_of_dyadicRange
      hfamily hlow (hterminal.le.trans hterminalHigh) hSsource hzeroS
      hSnonempty hbudget
      hcanonical hinterval (hfoldn h hlow hterminal)
      (hlarge h hlow hterminal)
  · simpa only [ratio] using hcapLarge

/-- Fully explicit interval version of the source crossing.  The low prefix
is eliminated in favor of the elementary `2^low * n + 1` interval bound. -/
theorem positiveDyadicThreshold_le_card_sums_of_dyadicRange_sourceInterval
    {source W S : Finset ℤ}
    {low high terminal deletionBudget cap D n propernessDenominator : ℕ}
    (hfamily : PreprocessingBilu.DyadicRangeSourceHApproximationFamily
      source low high D 1
        (PreprocessingBilu.preprocessingScaleDen propernessDenominator))
    (hlowTerminal : low < terminal) (hterminalHigh : terminal ≤ high)
    (hSsource : insert 0 S ⊆ source) (hSW : insert 0 S ⊆ W)
    (hzeroS : 0 ∉ S) (hSnonempty : S.Nonempty)
    (hcapCard : cap ≤ S.card) (hcapBudget : cap ≤ deletionBudget)
    (hbudget : deletionBudget < S.card)
    (hstable : Stability.WeaklyStableFor (insert 0 S)
      (Stability.minimalBoxFamily W) deletionBudget D (n ^ 2))
    (hn : 0 < n)
    (hintervalSet : insert 0 S ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hfoldn : ∀ h, low ≤ h → h < terminal → 2 ^ h ≤ n)
    (hlarge : ∀ h, low ≤ h → h < terminal →
      PreprocessingBilu.preprocessingIndexBound D propernessDenominator ≤
        2 ^ h)
    (hcapLarge :
      2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) +
          16 *
            (2 * (6 * PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ^ D *
              (4 * (4 * PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ^ D) + 1) *
            2 ^ terminal < cap) :
    positiveDyadicThreshold S deletionBudget terminal ≤
      (sums S cap).card := by
  apply positiveDyadicThreshold_le_card_sums_of_dyadicRange
    hfamily hlowTerminal hterminalHigh hSsource hSW hzeroS hSnonempty
      hcapCard hcapBudget hbudget hstable
  · intro z hz
    have hz' := Finset.mem_Icc.mp (hintervalSet hz)
    constructor
    · exact hz'.1
    · omega
  · exact hfoldn
  · exact hlarge
  · have hprefix := dyadicBinStart_le_sourceIntervalLog
      (low := low) hn hintervalSet hcapCard hcapBudget
    omega

end Greedy

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.Greedy.positiveDyadicThreshold_le_card_sums_of_dyadicRange
#print axioms
  Erdos186.CFP.Greedy.positiveDyadicThreshold_le_card_sums_of_dyadicRange_sourceInterval
