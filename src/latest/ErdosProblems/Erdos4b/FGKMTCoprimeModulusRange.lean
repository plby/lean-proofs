/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedCauchyError

/-!
# The retained error lies in the exceptional-prime coprime modulus range

Multiplication by the positive presieve modulus is injective. Every
resulting modulus stays coprime to an excluded factor of `M` when the
presieve modulus is coprime to that factor. Only nonnegative sums are
enlarged; no analytic distribution statement is assumed.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

def coprimeModulusDiscrepancySum (B0 L x : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 L).filter (fun q => q.Coprime B0), maxProgressionDiscrepancy x q

theorem coprimeModulusDiscrepancySum_nonneg (B0 L x : ℕ) :
    0 ≤ coprimeModulusDiscrepancySum B0 L x :=
  Finset.sum_nonneg fun q _ => maxProgressionDiscrepancy_nonneg x q

theorem sum_commonPinnedModulusRange_mul_le {W M R B0 L : ℕ}
    (hW : 0 < W) (hB0M : B0 ∣ M) (hWB0 : W.Coprime B0) (hL : W * R ^ 2 ≤ L)
    (F : ℕ → ℝ) (hF : ∀ q, 0 ≤ F q) :
    (∑ D ∈ commonPinnedModulusRange M R, F (W * D)) ≤
      ∑ q ∈ (Finset.Icc 1 L).filter (fun q => q.Coprime B0), F q := by
  classical
  rw [← Finset.sum_image (s := commonPinnedModulusRange M R) (g := fun D => W * D) (f := F)
    (fun D _ D' _ hDD' => Nat.eq_of_mul_eq_mul_left hW hDD')]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hDpos, hDR, _hsq, hcop⟩ := mem_commonPinnedModulusRange.mp hD
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hW hDpos,
      (Nat.mul_le_mul_left W hDR).trans hL⟩, ?_⟩
    exact Nat.coprime_mul_iff_left.mpr ⟨hWB0, hcop.of_dvd_right hB0M⟩
  · intro q _hq _hnot
    exact hF q

theorem commonPinnedDiscrepancySum_le_coprime {W M R A B B0 L : ℕ}
    (hW : 0 < W) (hB0M : B0 ∣ M) (hWB0 : W.Coprime B0) (hL : W * R ^ 2 ≤ L) :
    commonPinnedDiscrepancySum W M R A B ≤
      coprimeModulusDiscrepancySum B0 L B + coprimeModulusDiscrepancySum B0 L A := by
  have h := sum_commonPinnedModulusRange_mul_le hW hB0M hWB0 hL
    (fun q => maxProgressionDiscrepancy B q + maxProgressionDiscrepancy A q)
    (fun q => add_nonneg (maxProgressionDiscrepancy_nonneg B q)
      (maxProgressionDiscrepancy_nonneg A q))
  simpa only [commonPinnedDiscrepancySum, coprimeModulusDiscrepancySum,
    Finset.sum_add_distrib] using h

theorem commonPinnedCauchyEnvelope_le_coprime {m W M R A B B0 L : ℕ}
    (hW : 0 < W) (hB0M : B0 ∣ M) (hWB0 : W.Coprime B0) (hL : W * R ^ 2 ≤ L) :
    commonPinnedCauchyEnvelope m W M R A B ≤
      Real.sqrt (3 * ((A : ℝ) + B + 2) * (1 + Real.log (R ^ 2 : ℕ)) ^ (2 * (3 * m) ^ 2)) *
        Real.sqrt (coprimeModulusDiscrepancySum B0 L B + coprimeModulusDiscrepancySum B0 L A) := by
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (commonPinnedDiscrepancySum_le_coprime hW hB0M hWB0 hL))
    (Real.sqrt_nonneg _)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedDiscrepancySum_le_coprime
#print axioms Erdos4b.FGKMT.commonPinnedCauchyEnvelope_le_coprime
