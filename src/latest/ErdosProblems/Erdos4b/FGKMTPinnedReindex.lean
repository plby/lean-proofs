/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTScalarReindex
import ErdosProblems.Erdos4b.FGKMTPinnedSlice

/-! # The exact arithmetic one-dimensional sum in the pinned amplitude -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem pinnedUnshiftedValue_eq_sum_Icc {m M R N : ℕ} (hm : 1 ≤ m) (hR : 1 < R)
    (hRN : R ≤ N) (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (j : Fin (m + 1)) (r : commonPrimeUniverse M N → Option (Fin m)) :
    pinnedUnshiftedValue m R (fun q => q.val) j r =
      (pinnedBaseFactor (fun q => q.val) r * pinnedBaseEulerProduct (fun q => q.val) r) *
        ∑ a ∈ Finset.Icc 0 R,
          sieveProfile (m + 1) (m + 1) (Fin.cons (Real.log a / Real.log R)
            (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r))) *
          roughSieveWeight (M * assignmentPrimeProduct (fun q => q.val) r)
            (fun l => pinnedLocalDenominator (m + 1) l) a := by
  rw [pinnedUnshiftedValue_eq_rough hm commonPrimeUniverse_prime Subtype.val_injective
    commonPrimeUniverse_not_dvd (commonPrimeUniverse_large hsmall)]
  simp only [sieveProfile_pinnedBaseTuple]
  congr 1
  simp_rw [mul_comm (roughSieveWeight _ _ _)]
  apply sum_unit_assignments_rough_eq_sum_Icc (dvd_mul_right M _) hRN
    (fun l => pinnedLocalDenominator (m + 1) l)
    (fun a => sieveProfile (m + 1) (m + 1) (Fin.cons (Real.log a / Real.log R)
      (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r))))
  intro a _ha hRa
  exact sieveProfile_logSlice_zero_of_ge (m + 1) m hR _
    (sieveLogTuple_nonneg R _) hRa

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedUnshiftedValue_eq_sum_Icc
