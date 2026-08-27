/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFaceAssignmentVariation
import ErdosProblems.Erdos4b.FGKMTPinnedUniformProfile
import ErdosProblems.Erdos4b.FGKMTPinnedPairAlgebra

/-! # Pair variation for the original signed pinned amplitude -/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_commonPinnedProfile_pair_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      C * (m + 1 : ℕ) * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 ≤
        Real.log R →
      ∀ (j : Fin (m + 1)) (r s : commonPrimeUniverse M R → Option (Fin m)),
        SamePrimeSupport r s →
        |commonPinnedProfile m R (fun q => q.val) j r *
          (commonPinnedProfile m R (fun q => q.val) j s -
            commonPinnedProfile m R (fun q => q.val) j r)| ≤
          2 * (pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) *
            Real.log R) ^ 2 *
            primeAssignmentFaceMajorant (m + 1) m R (fun q => q.val) (commonAssignment r s) ^ 2 *
            ((C * sieveProfileScale (m + 1) / Real.log R) *
              Real.log (assignmentPrimeProduct (fun q => q.val) (movedAssignment r s)) +
                2 * (C * sieveProfileScale (m + 1) *
                  modulusLogScale (M * R) ^ 3 / Real.log R)) := by
  obtain ⟨Ce, hCe, hmean⟩ := exists_commonPinnedProfile_uniform_error
  obtain ⟨Cv, hCv, hvar⟩ := exists_primeAssignmentFaceProfile_variation_bound
  let C := Ce + Cv
  have hC : 0 < C := add_pos hCe hCv
  have heC : Ce ≤ C := le_add_of_nonneg_right hCv.le
  have hvC : Cv ≤ C := le_add_of_nonneg_left hCe.le
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall hcost j r s hrs
  let p : commonPrimeUniverse M R → ℕ := fun q => q.val
  let B := pinnedGlobalNormalization m M p
  let A := B * Real.log R
  let V := primeAssignmentFaceMajorant (m + 1) m R p
  let f := primeAssignmentFaceProfile (m + 1) m R p
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
  have hcoste : Ce * (m + 1 : ℕ) * sieveProfileScale (m + 1) *
      modulusLogScale (M * R) ^ 3 ≤ Real.log R := by
    apply le_trans _ hcost
    gcongr
  have hpoint (t : commonPrimeUniverse M R → Option (Fin m)) :
      |commonPinnedProfile m R p j t - A * f t| ≤ ε * A * V t := by
    have h := hmean hm hlog hM hR le_rfl hsmall hcoste j t
    have hV : 0 ≤ V t := majorantFaceValue_nonneg _ _ _
    calc
      _ ≤ Ce * B * modulusLogScale (M * R) ^ 3 * sieveProfileScale (m + 1) * V t := h
      _ ≤ C * B * modulusLogScale (M * R) ^ 3 * sieveProfileScale (m + 1) * V t := by gcongr
      _ = _ := by dsimp only [ε, A]; field_simp [hL.ne']
  have hp : ∀ q, 0 < p q := fun q => (commonPrimeUniverse_prime q).pos
  have hVr : V r ≤ V (commonAssignment r s) :=
    primeAssignmentFaceMajorant_le_common (Nat.succ_pos m) hlog m R hp r s
  have hVs : V s ≤ V (commonAssignment r s) := by
    rw [commonAssignment_comm r s]
    exact primeAssignmentFaceMajorant_le_common (Nat.succ_pos m) hlog m R hp s r
  have hdiff : |f s - f r| ≤
      ((C * sieveProfileScale (m + 1) / Real.log R) *
        Real.log (assignmentPrimeProduct p (movedAssignment r s))) * V (commonAssignment r s) := by
    have hV : 0 ≤ V (commonAssignment r s) := majorantFaceValue_nonneg _ _ _
    have hlogprod := Real.log_natCast_nonneg (assignmentPrimeProduct p (movedAssignment r s))
    rw [abs_sub_comm]
    calc
      _ ≤ (Cv * sieveProfileScale (m + 1) * V (commonAssignment r s)) *
          (Real.log (assignmentPrimeProduct p (movedAssignment r s)) / Real.log R) :=
        hvar _ (Nat.succ_pos m) hlog m R p hp r s hrs
      _ ≤ (C * sieveProfileScale (m + 1) * V (commonAssignment r s)) *
          (Real.log (assignmentPrimeProduct p (movedAssignment r s)) / Real.log R) := by gcongr
      _ = _ := by ring
  exact perturbed_profile_pair_bound hA (majorantFaceValue_nonneg _ _ _) hε hε1
    (sieveFaceProfile_nonneg _ _ _)
    (primeAssignmentFaceProfile_le_common (Nat.succ_pos m) hlog m R hp r s)
    ((hpoint r).trans (mul_le_mul_of_nonneg_left hVr (mul_nonneg hε hA)))
    ((hpoint s).trans (mul_le_mul_of_nonneg_left hVs (mul_nonneg hε hA))) hdiff

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedProfile_pair_bound
