/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedUniformProfile
import ErdosProblems.Erdos4b.FGKMTFaceAssignmentMean
import ErdosProblems.Erdos4b.FGKMTWeightedSquareError

/-! # Replacing the actual pinned diagonal by the true face-profile diagonal -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def commonPinnedDiagonal (m M R : ℕ) (j : Fin (m + 1)) : ℝ :=
  ∑ r : commonPrimeUniverse M R → Option (Fin m),
    commonPinnedProfile m R (fun q => q.val) j r ^ 2 *
      roughSieveWeight M (actualSieveDenominator false (m + 1))
        (assignmentPrimeProduct (fun q => q.val) r)

def commonPinnedFaceMajorantSum (m M R : ℕ) : ℝ :=
  ∑ r : commonPrimeUniverse M R → Option (Fin m),
    majorantFaceValue (m + 1) m (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r)) ^ 2 *
      roughSieveWeight M (actualSieveDenominator false (m + 1))
        (assignmentPrimeProduct (fun q => q.val) r)

theorem commonPinnedDiagonal_eq_row (m M R : ℕ) (j : Fin (m + 1)) :
    commonPinnedDiagonal m M R j =
      ∑ r : commonPrimeUniverse M R → Option (Fin m),
        commonPinnedProfile m R (fun q => q.val) j r ^ 2 /
          assignmentRowWeight (fun q => (q.val : ℝ) - 1) r := by
  apply Finset.sum_congr rfl
  intro r _hr
  have hweight : roughSieveWeight M (actualSieveDenominator false (m + 1))
      (assignmentPrimeProduct (fun q : commonPrimeUniverse M R => q.val) r) =
      1 / assignmentRowWeight (fun q => (q.val : ℝ) - 1) r := by
    rw [roughSieveWeight_apply_of_squarefree_coprime
      (assignmentPrimeProduct_squarefree commonPrimeUniverse_prime Subtype.val_injective r)
      (assignmentPrimeProduct_coprime commonPrimeUniverse_prime commonPrimeUniverse_not_dvd r).symm,
      commonPinnedRowWeight_eq_primeFactors commonPrimeUniverse_prime Subtype.val_injective r]
    simp [actualSieveDenominator]
  rw [hweight]
  simp only [div_eq_mul_inv, one_mul]

theorem exists_commonPinnedDiagonal_replacement_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      C * (m + 1 : ℕ) * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 ≤
        Real.log R →
      ∀ j : Fin (m + 1),
        |commonPinnedDiagonal m M R j -
          (pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) *
            Real.log R) ^ 2 * commonFaceDiagonal m M R| ≤
          3 * (C * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 / Real.log R) *
            (pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) *
              Real.log R) ^ 2 * commonPinnedFaceMajorantSum m M R := by
  obtain ⟨C, hC, hmean⟩ := exists_commonPinnedProfile_uniform_error
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall hcost j
  let p : commonPrimeUniverse M R → ℕ := fun q => q.val
  let B := pinnedGlobalNormalization m M p
  let A := B * Real.log R
  let ε := C * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 / Real.log R
  have hT : 0 ≤ sieveProfileScale (m + 1) :=
    zero_le_one.trans (profile_scales_bounds (Nat.succ_pos m) hlog).1
  have hD : 0 ≤ modulusLogScale (M * R) := zero_le_one.trans (one_le_modulusLogScale _)
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hB : 0 ≤ B :=
    (show (0 : ℝ) ≤ ((M.totient : ℝ) / M) / 2 by positivity).trans
      (pinnedGlobalNormalization_bounds (seven_le_of_profile_log hlog) hM hsmall
        commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd).1
  have hA : 0 ≤ A := mul_nonneg hB hL.le
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by
    apply (div_le_iff₀ hL).mpr
    rw [one_mul]
    calc
      _ ≤ C * (m + 1 : ℕ) * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 := by
        conv_lhs => rw [← mul_one C]
        gcongr
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
      _ ≤ _ := hcost
  have hchain := actualSieveDenominator_chain (by omega : 2 ≤ m + 1)
    (by omega : 1 ≤ m + 1) hsmall false
  have hg (l : ℕ) (hl : l.Prime) (hlM : ¬l ∣ M) :
      0 ≤ actualSieveDenominator false (m + 1) l := by
    have h := (hchain 0 (by omega) l hl hlM).1
    simp only [Nat.cast_zero, add_zero] at h
    exact (half_pos (show (0 : ℝ) < l by exact_mod_cast hl.pos)).le.trans h
  apply weighted_square_error hA hε hε1
    (commonPinnedProfile m R p j)
    (fun r => sieveFaceProfile (m + 1) m (sieveLogTuple R (assignmentPrimeTuple p r)))
    (fun r => majorantFaceValue (m + 1) m (sieveLogTuple R (assignmentPrimeTuple p r)))
    (fun r => roughSieveWeight M (actualSieveDenominator false (m + 1))
      (assignmentPrimeProduct p r))
    (fun r => sieveFaceProfile_nonneg _ _ _)
    (fun r => sieveFaceProfile_le_majorant (Nat.succ_pos m) hlog _ _)
    (fun r => roughSieveWeight_nonneg M _ hg _)
  intro r
  have h := hmean hm hlog hM hR le_rfl hsmall hcost j r
  convert h using 1
  dsimp only [ε, A, B]
  field_simp [hL.ne']
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedDiagonal_eq_row
#print axioms Erdos4b.FGKMT.exists_commonPinnedDiagonal_replacement_error
