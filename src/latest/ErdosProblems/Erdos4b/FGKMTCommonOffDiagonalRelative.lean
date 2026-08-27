/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteWeightedMajorant
import ErdosProblems.Erdos4b.FGKMTCommonMainTerm

/-!
# Relative off-diagonal error for the actual common coefficient vector

The finite prime universe, majorant support, arithmetic mean, Euler
normalization and moved-prime masses are all discharged. The result is
normalized by the literal positive diagonal main term.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_commonSieveQuadratic_offDiagonal_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      (k : ℝ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      |commonSieveQuadratic k M R - commonSieveDiagonal k M R| / commonSieveMainTerm k M R ≤
        C * (k : ℝ) ^ 3 * sieveProfileScale k / Real.log R := by
  obtain ⟨Cm, hCm, hmajor⟩ := exists_absoluteAssignmentMajorantSum_energy_bound
  obtain ⟨Ce, hCe, herror⟩ := exists_commonSieveCoefficient_offDiagonal_mass_bound
  let C := Cm + 12 * Real.exp 4 * Ce
  have hC : 0 < C := by dsimp only [C]; positivity
  have hmC : Cm ≤ C := le_add_of_nonneg_right (by positivity)
  have heC : 12 * Real.exp 4 * Ce ≤ C := le_add_of_nonneg_left hCm.le
  refine ⟨C, hC, ?_⟩
  intro k M R hk hlog hM hR hsmall htotal
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hΛ : 0 ≤ modulusLogScale (M * R ^ (2 * k)) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hT : 0 ≤ sieveProfileScale k :=
    zero_le_one.trans (profile_scales_bounds (by omega : 0 < k) hlog).1
  have hmain := commonSieveMainTerm_pos hk hlog hM hR hsmall
  have htotalm : (k : ℝ) *
      (Cm * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 := by
    refine le_trans ?_ htotal
    gcongr
  let p := fun q : commonPrimeUniverse M R => q.val
  have hraw : |commonSieveQuadratic k M R - commonSieveDiagonal k M R| ≤
      (Ce * k * sieveProfileScale k / Real.log R) * absoluteAssignmentMajorantSum k R p := by
    simpa only [commonSieveQuadratic, commonSieveDiagonal_eq_row] using
      herror (commonPrimeUniverse M R) hk hlog R p Subtype.val_injective
        (commonPrimeUniverse_large hsmall)
  have hB : absoluteAssignmentMajorantSum k R p ≤
      (12 * Real.exp 4 * (k : ℝ) ^ 2) * commonSieveMainTerm k M R := by
    calc
      _ ≤ 12 * Real.exp 4 * (k : ℝ) ^ 2 *
          multivariateSieveConstant M (fun q => (q : ℝ) - k) k * Real.log R ^ k *
            dimensionProfileEnergy k k :=
        hmajor (commonPrimeUniverse M R) hk hlog hM hR hsmall htotalm p
          commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd
      _ = _ := by unfold commonSieveMainTerm actualSieveDenominator; simp only [Bool.false_eq_true,
        if_false]; ring
  apply (div_le_iff₀ hmain).mpr
  calc
    _ ≤ (Ce * k * sieveProfileScale k / Real.log R) * absoluteAssignmentMajorantSum k R p := hraw
    _ ≤ (Ce * k * sieveProfileScale k / Real.log R) *
        ((12 * Real.exp 4 * (k : ℝ) ^ 2) * commonSieveMainTerm k M R) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (12 * Real.exp 4 * Ce) * (k : ℝ) ^ 3 * sieveProfileScale k / Real.log R *
        commonSieveMainTerm k M R := by ring
    _ ≤ _ := by gcongr

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonSieveQuadratic_offDiagonal_relative_error
