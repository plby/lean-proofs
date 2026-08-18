/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyDyadicRange

/-!
# Common physical target from the source dyadic range

This is the source-facing adapter from the whole-range Bilu package to the
varying-level physical target theorem.  Its only remaining greedy input is
the actual per-colour crossing; every approximation and numerical
inequality is constructed here.
-/

namespace Erdos186.CFP

noncomputable section

namespace RandomPartition

/-- Every colour-dependent crossing in the exact Bilu dyadic range reaches
one common physical target. -/
theorem exists_common_physicalTargetRun_of_dyadicRange
    {source W A : Finset ℤ}
    {q x D n low high H M cap propernessDenominator : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (level : Fin (q + 1) → ℕ)
    (hfamily : PreprocessingBilu.DyadicRangeSourceHApproximationFamily
      source low high D 1
        (PreprocessingBilu.preprocessingScaleDen propernessDenominator))
    (hzeroA : 0 ∉ A) (hsource : insert 0 A ⊆ source)
    (hAW : insert 0 A ⊆ W)
    (hcap : ∀ i, cap ≤ (integerColorClass A c i).card)
    (hbudget : ∀ i, x < (integerColorClass A c i).card)
    (hcross : ∀ i, Greedy.dyadicBinStart
      (integerColorClass A c i) x cap (level i) < cap)
    (hstable : ∀ i, Stability.WeaklyStableFor
      (anchoredColorClass A c i) (Stability.minimalBoxFamily W)
        x D (n ^ 2))
    (hlow : ∀ i, low ≤ level i) (hhigh : ∀ i, level i ≤ high)
    (hfoldn : ∀ i, 2 ^ level i ≤ n)
    (hinterval : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (hlarge : ∀ i,
      PreprocessingBilu.preprocessingIndexBound D propernessDenominator ≤
        2 ^ level i)
    (hpropernessDenominator : 0 < propernessDenominator)
    (hHM : ∀ i, H ≤ M * 2 ^ level i)
    (hglobalLarge :
      8 * (M + 1) ^ D *
          (2 * PreprocessingBilu.preprocessingScaleDen
            propernessDenominator) ^ D ≤
        (GrowthLemmas.multifoldSumset H W).card) :
    ∃ target : ℕ, ∃ run : ∀ i, Greedy.PhysicalTargetRun
        (integerColorClass A c i) cap target,
      (GrowthLemmas.multifoldSumset H W).card ≤
        2 * (8 * (M + 1) ^ D *
          (2 * PreprocessingBilu.preprocessingScaleDen
            propernessDenominator) ^ D) * target ∧
      target = Greedy.physicalDensityTarget
        (GrowthLemmas.multifoldSumset H W).card
        (8 * (M + 1) ^ D *
          (2 * PreprocessingBilu.preprocessingScaleDen
            propernessDenominator) ^ D) := by
  apply exists_common_physicalTargetRun_of_rankFlexible_threshold
    (scaleNum := 1)
    (scaleDen := PreprocessingBilu.preprocessingScaleDen
      propernessDenominator)
    c level hzeroA hAW hcap hcross hstable hfoldn
    hinterval
  · intro i B hBsubset hBcard
    have hBnonempty : B.Nonempty := by
      by_contra hnot
      have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
      rw [hBempty] at hBcard
      simp only [Finset.card_empty, zero_add] at hBcard
      exact (Nat.not_lt_of_ge hBcard) (hbudget i)
    have hanchoredBNe : insert 0 B ≠ {0} := by
      intro heq
      obtain ⟨z, hz⟩ := hBnonempty
      have hz0 : z = 0 := by
        have : z ∈ ({0} : Finset ℤ) := by
          rw [← heq]
          exact Finset.mem_insert_of_mem hz
        simpa using this
      subst z
      exact hzeroA (integerColorClass_subset A c i (hBsubset hz))
    simpa only [one_mul] using
      PreprocessingBilu.exists_HApproximation_numeric_of_dyadicRange
        hfamily (hlow i) (hhigh i)
          ((Finset.insert_subset_insert 0 hBsubset).trans
            ((Finset.insert_subset_insert 0
              (integerColorClass_subset A c i)).trans hsource))
          (by simp) hanchoredBNe (hlarge i)
  · simp only [PreprocessingBilu.preprocessingScaleDen]
    exact Nat.mul_pos (by omega) hpropernessDenominator
  · exact hHM
  · exact hglobalLarge

end RandomPartition

end


end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_common_physicalTargetRun_of_dyadicRange
