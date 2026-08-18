/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource
import ErdosProblems.Erdos186.CFP.GreedyPhysicalDensity

/-!
# Greedy threshold inputs from the exact source dyadic range

This module turns the Bilu--Freiman range package into the two concrete
inputs used independently at every colour level: a positive-rank
approximation with its numerical inequality, and the consecutive positive
threshold ratio.  No common level or common approximation rank is chosen.
-/

namespace Erdos186.CFP

noncomputable section

namespace PreprocessingBilu

/-- Extract a positive-rank approximation and its strict numerical
inequality at one level of the source dyadic range. -/
theorem exists_HApproximation_numeric_of_dyadicRange
    {A S : Finset ℤ}
    {low high D propernessDenominator level : ℕ}
    (hfamily : DyadicRangeSourceHApproximationFamily A low high D 1
      (preprocessingScaleDen propernessDenominator))
    (hlow : low ≤ level) (hhigh : level ≤ high)
    (hSA : S ⊆ A) (hzeroS : 0 ∈ S) (hSne : S ≠ {0})
    (hlarge : preprocessingIndexBound D propernessDenominator ≤
      2 ^ level) :
    ∃ rank : ℕ, 0 < rank ∧ rank ≤ D ∧
      ∃ V : HDimension.HApproximation S (2 ^ level) rank 1
          (preprocessingScaleDen propernessDenominator),
        (2 * preprocessingScaleDen propernessDenominator) ^ rank *
            (2 ^ level + 1) ^ (rank - 1) < (2 ^ level) ^ rank := by
  obtain ⟨rank, hrank, hrankD, hV⟩ :=
    hfamily level hlow hhigh hSA hzeroS hSne
  let V : HDimension.HApproximation S (2 ^ level) rank 1
      (preprocessingScaleDen propernessDenominator) := Classical.choice hV
  refine ⟨rank, hrank, hrankD, V, ?_⟩
  exact approximation_numeric_of_preprocessing_large
    V.scaleDen_pos hrank hrankD hlarge

end PreprocessingBilu

namespace Greedy

/-- The exact source range discharges the consecutive-threshold comparison
at an arbitrary colour-dependent level. -/
theorem positiveDyadicThreshold_succ_le_of_dyadicRange
    {source S : Finset ℤ}
    {low high deletionBudget D n propernessDenominator level : ℕ}
    (hfamily : PreprocessingBilu.DyadicRangeSourceHApproximationFamily
      source low high D 1
        (PreprocessingBilu.preprocessingScaleDen propernessDenominator))
    (hlow : low ≤ level) (hhigh : level ≤ high)
    (hSsource : insert 0 S ⊆ source) (hzeroS : 0 ∉ S)
    (hSnonempty : S.Nonempty) (hbudget : deletionBudget < S.card)
    (hstable : Stability.WeaklyStableMinimalFor
      (insert 0 S) deletionBudget D n)
    (hinterval : ∀ z ∈ insert 0 S, 0 ≤ z ∧ z < (n : ℤ))
    (hfoldn : 2 ^ level ≤ n)
    (hlarge : PreprocessingBilu.preprocessingIndexBound D
      propernessDenominator ≤ 2 ^ level) :
    positiveDyadicThreshold S deletionBudget (level + 1) ≤
      (2 * (6 * PreprocessingBilu.preprocessingScaleDen
          propernessDenominator) ^ D *
        (4 * (4 * PreprocessingBilu.preprocessingScaleDen
          propernessDenominator) ^ D) + 1) *
        positiveDyadicThreshold S deletionBudget level := by
  have hanchoredNe : insert 0 S ≠ {0} := by
    intro heq
    obtain ⟨z, hz⟩ := hSnonempty
    have hz0 : z = 0 := by
      have : z ∈ ({0} : Finset ℤ) := by
        rw [← heq]
        exact Finset.mem_insert_of_mem hz
      simpa using this
    subst z
    exact hzeroS hz
  obtain ⟨dA, hdA, hdAD, hWA⟩ :=
    hfamily level hlow hhigh hSsource (by simp) hanchoredNe
  let WA : HDimension.HApproximation (insert 0 S) (2 ^ level) dA 1
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) :=
    Classical.choice hWA
  apply positiveDyadicThreshold_succ_le_of_approximations
    hzeroS hstable hinterval WA hdA hdAD hfoldn
  intro B hBS hBcard
  have hBnonempty : B.Nonempty := by
    by_contra hnot
    have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hBempty] at hBcard
    simp only [Finset.card_empty, zero_add] at hBcard
    omega
  have hanchoredBNe : insert 0 B ≠ {0} := by
    intro heq
    obtain ⟨z, hz⟩ := hBnonempty
    have hz0 : z = 0 := by
      have : z ∈ ({0} : Finset ℤ) := by
        rw [← heq]
        exact Finset.mem_insert_of_mem hz
      simpa using this
    subst z
    exact hzeroS (hBS hz)
  simpa only [one_mul] using
    PreprocessingBilu.exists_HApproximation_numeric_of_dyadicRange
      hfamily hlow hhigh
        ((Finset.insert_subset_insert 0 hBS).trans hSsource)
        (by simp) hanchoredBNe hlarge

end Greedy

end


end Erdos186.CFP

#print axioms
  Erdos186.CFP.Greedy.positiveDyadicThreshold_succ_le_of_dyadicRange
