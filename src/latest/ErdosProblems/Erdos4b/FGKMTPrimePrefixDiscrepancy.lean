/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeProgressionEnvelope

/-!
# Literal prime-counting discrepancies at every endpoint

The endpoint maximum is taken separately at each modulus. Its Abel bound
uses the existing centered theta maximum, so the excluded prime never
depends on an endpoint chosen later by the sieve.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

def maxPrimeProgressionDiscrepancyUpTo (x q : ℕ) : ℝ :=
  if hx : 2 ≤ x then
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx)
      (fun y => maxProgressionDiscrepancy y q)
  else 0

theorem maxPrimeProgressionDiscrepancyUpTo_nonneg (x q : ℕ) :
    0 ≤ maxPrimeProgressionDiscrepancyUpTo x q := by
  by_cases hx : 2 ≤ x
  · rw [maxPrimeProgressionDiscrepancyUpTo, dif_pos hx]
    exact (maxProgressionDiscrepancy_nonneg 2 q).trans
      (Finset.le_sup' (fun y => maxProgressionDiscrepancy y q)
        (Finset.mem_Icc.mpr ⟨le_rfl, hx⟩))
  · simp [maxPrimeProgressionDiscrepancyUpTo, hx]

theorem maxProgressionDiscrepancy_eq_zero_of_lt_two {x : ℕ} (hx : x < 2) (q : ℕ) :
    maxProgressionDiscrepancy x q = 0 := by
  have hcount (a : ℕ) : primeCountUpTo x q a = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hn, hp, _⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hn
    have hp2 := hp.two_le
    omega
  have htotal : primeCountTotal x = 0 := by
    interval_cases x <;> norm_num [primeCountTotal]
  have hdisc : progressionDiscrepancy x q = fun _ => 0 := by
    funext a
    simp [progressionDiscrepancy, hcount, htotal]
  simp [maxProgressionDiscrepancy, hdisc]

theorem maxProgressionDiscrepancy_le_prefix {y x : ℕ} (hyx : y ≤ x) (q : ℕ) :
    maxProgressionDiscrepancy y q ≤ maxPrimeProgressionDiscrepancyUpTo x q := by
  by_cases hy : 2 ≤ y
  · rw [maxPrimeProgressionDiscrepancyUpTo, dif_pos (hy.trans hyx)]
    exact Finset.le_sup' (fun t => maxProgressionDiscrepancy t q)
      (Finset.mem_Icc.mpr ⟨hy, hyx⟩)
  · rw [maxProgressionDiscrepancy_eq_zero_of_lt_two (by omega) q]
    exact maxPrimeProgressionDiscrepancyUpTo_nonneg x q

theorem maxPrimeProgressionDiscrepancyUpTo_mono {x y : ℕ} (hxy : x ≤ y) (q : ℕ) :
    maxPrimeProgressionDiscrepancyUpTo x q ≤ maxPrimeProgressionDiscrepancyUpTo y q := by
  by_cases hx : 2 ≤ x
  · rw [maxPrimeProgressionDiscrepancyUpTo, dif_pos hx]
    apply Finset.sup'_le
    intro t ht
    exact maxProgressionDiscrepancy_le_prefix ((Finset.mem_Icc.mp ht).2.trans hxy) q
  · simpa [maxPrimeProgressionDiscrepancyUpTo, hx] using
      maxPrimeProgressionDiscrepancyUpTo_nonneg y q

private theorem thetaPrefix_mono {y x : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x) (q : ℕ) :
    maxCenteredThetaProgressionDiscrepancyUpTo y q ≤
      maxCenteredThetaProgressionDiscrepancyUpTo x q := by
  simp only [maxCenteredThetaProgressionDiscrepancyUpTo, dif_pos hy, dif_pos (hy.trans hyx)]
  apply Finset.sup'_le
  intro t ht
  exact Finset.le_sup' (fun t => maxCenteredThetaProgressionDiscrepancy t q) (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2.trans hyx⟩)

theorem maxPrimeProgressionDiscrepancyUpTo_le_centered {x q : ℕ}
    (hx : 2 ≤ x) (hq : 1 ≤ q) :
    maxPrimeProgressionDiscrepancyUpTo x q ≤ (Real.log 2)⁻¹ *
      (maxCenteredProgressionDiscrepancyUpTo x q +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
  have hinv : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr (Real.log_pos one_lt_two)).le
  rw [maxPrimeProgressionDiscrepancyUpTo, dif_pos hx]
  apply Finset.sup'_le
  intro y hy
  obtain ⟨hy2, hyx⟩ := Finset.mem_Icc.mp hy
  exact (maxProgressionDiscrepancy_le_inv_log_two_mul_maxCenteredThetaUpTo hy2 hq).trans
    (mul_le_mul_of_nonneg_left ((thetaPrefix_mono hy2 hyx q).trans
      (maxCenteredThetaProgressionDiscrepancyUpTo_le hq)) hinv)

def coprimePrimeDiscrepancyPrefixSum (B L x : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 L).filter (fun q => q.Coprime B),
    maxPrimeProgressionDiscrepancyUpTo x q

theorem coprimePrimeDiscrepancyPrefixSum_nonneg (B L x : ℕ) :
    0 ≤ coprimePrimeDiscrepancyPrefixSum B L x :=
  Finset.sum_nonneg fun q _ => maxPrimeProgressionDiscrepancyUpTo_nonneg x q

theorem coprimePrimeDiscrepancyPrefixSum_mono_modulus {L L' : ℕ} (hL : L ≤ L') (B x : ℕ) :
    coprimePrimeDiscrepancyPrefixSum B L x ≤ coprimePrimeDiscrepancyPrefixSum B L' x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hqI, hqB⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hqL⟩ := Finset.mem_Icc.mp hqI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hqL.trans hL⟩, hqB⟩
  · intro q _ _
    exact maxPrimeProgressionDiscrepancyUpTo_nonneg x q

theorem coprimeModulusDiscrepancySum_le_prefix {y x : ℕ} (hyx : y ≤ x) (B L : ℕ) :
    coprimeModulusDiscrepancySum B L y ≤ coprimePrimeDiscrepancyPrefixSum B L x :=
  Finset.sum_le_sum fun q _ => maxProgressionDiscrepancy_le_prefix hyx q

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.maxPrimeProgressionDiscrepancyUpTo_le_centered
#print axioms Erdos4b.FGKMT.coprimeModulusDiscrepancySum_le_prefix
