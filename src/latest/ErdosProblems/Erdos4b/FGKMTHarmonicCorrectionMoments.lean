/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRoughMoments
import ErdosProblems.Erdos4b.FGKMTBoundaryLogMoment
import ErdosProblems.Erdos4b.FGKMTHarmonicMean

/-!
# Full correction moments and the quantitative cumulative sieve sum

The rough and boundary estimates combine with the exact convolution
identity. The bound is uniform in the dimension and keeps only the
explicit totient ratio and prime-log divisor mass of the modulus.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem harmonicCorrection_roughSieveWeight_moments {k M : ℕ}
    (hk : 0 < k) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) :
    Summable (fun n => |harmonicCorrection (roughSieveWeight M g) n|) ∧
      (∑' n, |harmonicCorrection (roughSieveWeight M g) n|) ≤
        Real.exp 12 * ((M : ℝ) / M.totient) ∧
      Summable (fun n => |harmonicCorrection (roughSieveWeight M g) n| * Real.log n) ∧
      (∑' n, |harmonicCorrection (roughSieveWeight M g) n| * Real.log n) ≤
        Real.exp 12 * ((M : ℝ) / M.totient) *
          (4 + ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ)) := by
  obtain ⟨hr, hrA, hrLog, hrL⟩ := roughHarmonicCorrection_moments hk hsmall g hg hclose
  have hb := (preSieveBoundary_absolute_sum_bound hM.ne').1
  have hbA := preSieveBoundary_abs_tsum_le_totientRatio hM
  have hbLog := preSieveBoundary_log_summable hM.ne'
  have hbL := preSieveBoundary_log_tsum_le hM
  obtain ⟨hs, hA⟩ := arithmetic_mul_abs_summable_and_tsum_le
    (roughHarmonicCorrection M g) (preSieveBoundary M) hr hb
  obtain ⟨hsLog, hL⟩ := arithmetic_mul_log_summable_and_tsum_le
    (roughHarmonicCorrection M g) (preSieveBoundary M) hr hb hrLog hbLog
  have hb0 : (0 : ℝ) ≤ ∑' n, |preSieveBoundary M n| :=
    tsum_nonneg (fun n => abs_nonneg _)
  have hbLog0 : (0 : ℝ) ≤ ∑' n, |preSieveBoundary M n| * Real.log n :=
    tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg n))
  simp only [harmonicCorrection_roughSieveWeight_eq]
  refine ⟨hs, hA.trans (mul_le_mul hrA hbA hb0 (Real.exp_pos _).le), hsLog, ?_⟩
  calc
    _ ≤ (4 * Real.exp 12) * ((M : ℝ) / M.totient) +
        Real.exp 12 * (((M : ℝ) / M.totient) *
          ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ)) :=
      hL.trans (add_le_add (mul_le_mul hrL hbA hb0 (by positivity))
        (mul_le_mul hrA hbL hbLog0 (Real.exp_pos _).le))
    _ = _ := by ring

/-- The full harmonic main constant and a uniform explicit error at every
positive integer endpoint. No dimension-dependent convergence threshold
appears in this estimate. -/
theorem roughSieveWeight_cumulative_error_le {k M N : ℕ}
    (hk : 0 < k) (hM : 0 < M) (hN : 1 ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) :
    |(∑ n ∈ Finset.Ioc 0 N, roughSieveWeight M g n) -
      (∑' n, harmonicCorrection (roughSieveWeight M g) n) * Real.log N| ≤
        Real.exp 12 * ((M : ℝ) / M.totient) *
          (5 + ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ)) := by
  obtain ⟨hs, hA, hsLog, hL⟩ := harmonicCorrection_roughSieveWeight_moments
    hk hM hsmall g hg hclose
  calc
    _ ≤ (∑' n, |harmonicCorrection (roughSieveWeight M g) n|) +
        ∑' n, |harmonicCorrection (roughSieveWeight M g) n| * Real.log n :=
      sum_sub_harmonicCorrection_tsum_log_le _ hs hsLog hN
    _ ≤ Real.exp 12 * ((M : ℝ) / M.totient) +
        Real.exp 12 * ((M : ℝ) / M.totient) *
          (4 + ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ)) := add_le_add hA hL
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.roughSieveWeight_cumulative_error_le
