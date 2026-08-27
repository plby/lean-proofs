/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonDiagonalMean
import ErdosProblems.Erdos4b.FGKMTAssignmentDiagonal

/-! # The literal common-coefficient quadratic and its positive main term -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def commonSieveQuadratic (k M R : ℕ) : ℝ :=
  finiteSieveQuadratic (fun q : commonPrimeUniverse M R => (q.val : ℝ))
    (commonSieveCoefficient k R (fun q => q.val))

def commonSieveMainTerm (k M R : ℕ) : ℝ :=
  multivariateSieveConstant M (actualSieveDenominator false k) k * Real.log R ^ k *
    dimensionProfileEnergy k k

theorem commonSieveMainTerm_pos {k M R : ℕ} (hk : 2 ≤ k)
    (hlog : 10000 ≤ Real.log k) (hM : 0 < M) (hR : 1 < R)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    0 < commonSieveMainTerm k M R := by
  have hP := multivariateSieveConstant_pos (by omega : 0 < k) hM
    (fun p hp hpk => hsmall p hp (by omega)) _ (actualSieveDenominator_chain hk le_rfl hsmall false)
  have hI := dimensionProfileEnergy_pos (by omega : 0 < k) hlog (le_refl k)
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  exact mul_pos (mul_pos hP (pow_pos hL k)) hI

theorem commonSieveDiagonal_eq_row (k M R : ℕ) :
    commonSieveDiagonal k M R =
      ∑ r : commonPrimeUniverse M R → Option (Fin k),
        primeAssignmentProfile k R (fun q => q.val) r ^ 2 /
          assignmentRowWeight (fun q => (q.val : ℝ)) r := by
  unfold commonSieveDiagonal
  apply Finset.sum_congr rfl
  intro r _hr
  rw [div_eq_mul_one_div, assignmentRowWeight_inv_eq_rough commonPrimeUniverse_prime
    Subtype.val_injective commonPrimeUniverse_not_dvd r]
  rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonSieveMainTerm_pos
#print axioms Erdos4b.FGKMT.commonSieveDiagonal_eq_row
