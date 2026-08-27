/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedProfileMean
import ErdosProblems.Erdos4b.FGKMTFaceProfile

/-! # A single tuple-independent error envelope for the pinned profile -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_commonPinnedProfile_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R N : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R → R ≤ N →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      C * (m + 1 : ℕ) * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 ≤
        Real.log R →
      ∀ (j : Fin (m + 1)) (r : commonPrimeUniverse M N → Option (Fin m)),
        |commonPinnedProfile m R (fun q => q.val) j r -
          pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M N => q.val) *
            Real.log R * sieveFaceProfile (m + 1) m
              (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r))| ≤
          C * pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M N => q.val) *
            modulusLogScale (M * R) ^ 3 * sieveProfileScale (m + 1) *
              majorantFaceValue (m + 1) m
                (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r)) := by
  obtain ⟨C, hC, hmean⟩ := exists_commonPinnedProfile_face_error
  refine ⟨C, hC, ?_⟩
  intro m M R N hm hlog hM hR hRN hsmall hcost j r
  let p : commonPrimeUniverse M N → ℕ := fun q => q.val
  have hT : 0 ≤ sieveProfileScale (m + 1) :=
    zero_le_one.trans (profile_scales_bounds (Nat.succ_pos m) hlog).1
  have hB : 0 ≤ pinnedGlobalNormalization m M p :=
    (show (0 : ℝ) ≤ ((M.totient : ℝ) / M) / 2 by positivity).trans
      (pinnedGlobalNormalization_bounds (seven_le_of_profile_log hlog) hM hsmall
        commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd).1
  have hD : 0 ≤ modulusLogScale (M * R) := zero_le_one.trans (one_le_modulusLogScale _)
  have hDl : 0 ≤ modulusLogScale (M * assignmentPrimeProduct p r) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hV := majorantFaceValue_nonneg (m + 1) m (sieveLogTuple R (assignmentPrimeTuple p r))
  by_cases hr : assignmentPrimeProduct p r < R
  · have hscale : modulusLogScale (M * assignmentPrimeProduct p r) ≤ modulusLogScale (M * R) :=
      modulusLogScale_mono (Nat.mul_pos hM
        (assignmentPrimeProduct_pos (fun q => (commonPrimeUniverse_prime q).pos) r))
        (Nat.mul_le_mul_left M hr.le)
    have hlocal : C * (m + 1 : ℕ) * sieveProfileScale (m + 1) *
        modulusLogScale (M * assignmentPrimeProduct p r) ^ 3 ≤ Real.log R := by
      apply le_trans _ hcost
      gcongr
    have h := hmean hm hlog hM hR hRN hsmall j r hlocal
    rw [← sieveFaceProfile_eq_integral] at h
    refine h.trans ?_
    gcongr
  · have hy := commonPinnedProfile_zero_of_product_ge commonPrimeUniverse_prime
      Subtype.val_injective hR j r (by omega : R ≤ assignmentPrimeProduct p r)
    have hf := sieveFaceProfile_logTuple_zero_of_product_ge (k := m + 1) hR
      (assignmentPrimeTuple p r)
      (assignmentPrimeTuple_pos (fun q => (commonPrimeUniverse_prime q).pos) r)
      (by simpa only [prod_assignmentPrimeTuple] using (by omega : R ≤ assignmentPrimeProduct p r))
    change |commonPinnedProfile m R p j r - _ * _ * sieveFaceProfile _ _ _| ≤ _
    rw [hy, hf, mul_zero, sub_zero, abs_zero]
    positivity

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedProfile_uniform_error
