/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTGeneralLongTensorMean
import ErdosProblems.Erdos4b.FGKMTMixedDenominators

/-!
# The actual long-factor mean, with its full support

The profile hypotheses are all discharged at the intended scales.
The main term uses the original `log R`, the full long mass, and the
short masses. Rescaling changes neither that main term nor the sum.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_longTensorSieveSum_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → j + 1 ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      (j + 1 : ℕ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      |longTensorSieveSum k M (actualSieveDenominator pinned k) R j -
          multivariateSieveConstant M (actualSieveDenominator pinned k) (j + 1) *
            (Real.log R * dimensionLongMass k) * (Real.log R * dimensionProfileMass k) ^ j| /
        (multivariateSieveConstant M (actualSieveDenominator pinned k) (j + 1) *
          (Real.log R * dimensionLongMass k) * (Real.log R * dimensionProfileMass k) ^ j) ≤
        (j + 1 : ℕ) *
          (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_generalLongTensorSieveSum_relative_error
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hlog hM hR hj hsmall pinned htotal
  exact hbound hk hlog hM hR hj
    (fun p hp hpk => hsmall p hp (by omega)) (actualSieveDenominator pinned k)
    (actualSieveDenominator_chain hk hj hsmall pinned) htotal

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_longTensorSieveSum_relative_error
