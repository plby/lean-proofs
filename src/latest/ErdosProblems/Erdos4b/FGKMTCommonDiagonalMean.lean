/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentReindex
import ErdosProblems.Erdos4b.FGKMTCommonCoefficients
import ErdosProblems.Erdos4b.FGKMTDimensionMean

/-!
# Uniform relative mean of the actual common-coefficient diagonal

The assignment sum equals the literal natural-box cutoff sum, with no
approximation. The previously proved energy-normalized estimate therefore
applies with the same dimension-independent constant.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def commonSieveDiagonal (k M R : ℕ) : ℝ :=
  ∑ r : commonPrimeUniverse M R → Option (Fin k),
    primeAssignmentProfile k R (fun q => q.val) r ^ 2 *
      roughSieveWeight M (actualSieveDenominator false k)
        (assignmentPrimeProduct (fun q => q.val) r)

theorem commonSieveDiagonal_eq_cutoff {k M R : ℕ} (hR : 1 < R) :
    commonSieveDiagonal k M R =
      cutoffSieveSum M (actualSieveDenominator false k) R k
        (fun t => dimensionProfileFactor k t ^ 2) (fun t => sieveCutoff t ^ 2) 0 := by
  have hsupport (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hprod : R ≤ ∏ i, r i) :
      sieveProfile k k (sieveLogTuple R r) ^ 2 = 0 := by
    rw [sieveProfile_logTuple_zero_of_product_ge hR r hr hprod]
    norm_num
  calc
    _ = ∑ e : Fin k → Fin (R + 1),
        sieveProfile k k (sieveLogTuple R (fun i => (e i).val)) ^ 2 *
          roughSieveWeight M (actualSieveDenominator false k) (∏ i, (e i).val) :=
      sum_assignments_eq_sum_box k M R (actualSieveDenominator false k)
        (fun r => sieveProfile k k (sieveLogTuple R r) ^ 2) hsupport
    _ = _ := by
      unfold cutoffSieveSum
      apply Finset.sum_congr rfl
      intro e _he
      simp only [sieveProfile, sieveLogTuple, mul_pow, Finset.prod_pow, zero_add]
      ring

theorem exists_commonSieveDiagonal_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      (k : ℝ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 →
      |commonSieveDiagonal k M R -
        multivariateSieveConstant M (actualSieveDenominator false k) k * Real.log R ^ k *
          dimensionProfileEnergy k k| /
        (multivariateSieveConstant M (actualSieveDenominator false k) k * Real.log R ^ k *
          dimensionProfileEnergy k k) ≤
        (k : ℝ) *
          (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_dimensionProfile_energy_relative_error
  refine ⟨C, hC, ?_⟩
  intro k M R hk hlog hM hR hsmall htotal
  rw [commonSieveDiagonal_eq_cutoff hR]
  exact hbound hk hlog hM hR le_rfl hsmall false htotal

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonSieveDiagonal_eq_cutoff
#print axioms Erdos4b.FGKMT.exists_commonSieveDiagonal_relative_error
