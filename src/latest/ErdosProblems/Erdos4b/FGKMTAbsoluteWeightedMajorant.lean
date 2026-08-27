/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTGeneralWeightedMajorant
import ErdosProblems.Erdos4b.FGKMTAbsoluteEulerComparison
import ErdosProblems.Erdos4b.FGKMTAssignmentMajorantBox

/-!
# The absolute-kernel arithmetic majorant on the actual main-term scale

The generic full-box mean applies to both absolute denominator chains.
The Euler comparison changes the normalization by a fixed factor, not
one exponential in the number of coordinates.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_absoluteMajorantSieveSum_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j a : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → 1 ≤ a → a ≤ 2 → j + 1 + a ≤ k + 1 →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      (j + 1 : ℕ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      majorantSieveSum k M (absoluteSieveDenominator a k) R (j + 1) ≤
        12 * Real.exp 4 * (j + 1 : ℕ) ^ 2 *
          multivariateSieveConstant M (fun p => (p : ℝ) - k) (j + 1) *
          Real.log R ^ (j + 1) * dimensionProfileEnergy k (j + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_generalMajorantSieveSum_energy_bound
  refine ⟨C, hC, ?_⟩
  intro k M R j a hk hlog hM hR ha ha2 hj hsmall htotal
  have hjk : j + 1 ≤ k := by omega
  have hI := dimensionProfileEnergy_pos (by omega : 0 < k) hlog hjk
  have hL : 0 ≤ Real.log R ^ (j + 1) := pow_nonneg (Real.log_natCast_nonneg _) _
  have hratio := absolute_multivariateSieveConstant_le hk hM ha ha2 hj hsmall
  calc
    _ ≤ 12 * (j + 1 : ℕ) ^ 2 *
        multivariateSieveConstant M (absoluteSieveDenominator a k) (j + 1) *
          Real.log R ^ (j + 1) * dimensionProfileEnergy k (j + 1) :=
      hbound hk hlog hM hR hjk (fun p hp hpk => hsmall p hp (by omega)) _
        (absoluteSieveDenominator_chain hk ha ha2 hj hsmall) htotal
    _ ≤ 12 * (j + 1 : ℕ) ^ 2 *
        (Real.exp 4 * multivariateSieveConstant M (fun p => (p : ℝ) - k) (j + 1)) *
          Real.log R ^ (j + 1) * dimensionProfileEnergy k (j + 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by positivity)) hL) hI.le
    _ = _ := by ring

theorem exists_absoluteAssignmentMajorantSum_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] [Fintype α],
      ∀ {k M R : ℕ}, 2 ≤ k → 10000 ≤ Real.log k → 0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      (k : ℝ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      ∀ (p : α → ℕ), (∀ q, (p q).Prime) → Function.Injective p → (∀ q, ¬p q ∣ M) →
      absoluteAssignmentMajorantSum k R p ≤
        12 * Real.exp 4 * (k : ℝ) ^ 2 *
          multivariateSieveConstant M (fun p => (p : ℝ) - k) k *
          Real.log R ^ k * dimensionProfileEnergy k k := by
  obtain ⟨C, hC, hbound⟩ := exists_absoluteMajorantSieveSum_energy_bound
  refine ⟨C, hC, ?_⟩
  intro α _ _ k M R hk hlog hM hR hsmall htotal p hp hinj hpM
  have hdim : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  have hb := hbound (j := k - 1) (a := 1) hk hlog hM hR (by omega) (by omega)
    (by omega) hsmall (by simpa only [hdim] using htotal)
  exact (absoluteAssignmentMajorantSum_le_box (by omega : 0 < k) hlog hR hp hinj hpM).trans
    (by simpa only [hdim, Nat.cast_one] using hb)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_absoluteMajorantSieveSum_energy_bound
#print axioms Erdos4b.FGKMT.exists_absoluteAssignmentMajorantSum_energy_bound
