/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTGeneralWeightedMajorant
import ErdosProblems.Erdos4b.FGKMTLongTensorMean

/-!
# The arithmetic square-majorant sum

Finite Cauchy--Schwarz, coordinate permutation, and the proved mixed
mean give a uniform quadratic-dimensional upper bound on the literal
weighted majorant, normalized by the actual profile energy.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_majorantSieveSum_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → j + 1 ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      (j + 1 : ℕ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      majorantSieveSum k M (actualSieveDenominator pinned k) R (j + 1) ≤
        12 * (j + 1 : ℕ) ^ 2 *
          multivariateSieveConstant M (actualSieveDenominator pinned k) (j + 1) *
          Real.log R ^ (j + 1) * dimensionProfileEnergy k (j + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_generalMajorantSieveSum_energy_bound
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hlog hM hR hj hsmall pinned htotal
  exact hbound hk hlog hM hR hj
    (fun p hp hpk => hsmall p hp (by omega)) (actualSieveDenominator pinned k)
    (actualSieveDenominator_chain hk hj hsmall pinned) htotal

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.majorantSieveSum_le_long
#print axioms Erdos4b.FGKMT.exists_majorantSieveSum_energy_bound
