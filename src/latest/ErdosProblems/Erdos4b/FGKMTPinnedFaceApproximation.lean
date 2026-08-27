/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedUnshiftedMean
import ErdosProblems.Erdos4b.FGKMTPinnedNormalizationBounds

/-!
# The actual pinned profile with both approximation errors retained

This is a uniform bound for the original profile, not an independent
replacement coefficient. The remaining arithmetic majorant must still
be estimated before the final prime-mass theorem can be assembled.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem combine_pinned_face_errors {x y z A B : ℝ}
    (hxy : |x - y| ≤ A) (hyz : |y - z| ≤ B) : |x - z| ≤ A + B :=
  (abs_sub_le x y z).trans (add_le_add hxy hyz)

theorem exists_commonPinnedProfile_face_error_split :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {m M R N : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
        0 < M → 1 < R → R ≤ N →
        (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
        ∀ (j : Fin (m + 1)) (r : commonPrimeUniverse M N → Option (Fin m)),
          |commonPinnedProfile m R (fun q => q.val) j r -
            pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M N => q.val) *
              Real.log R * (∫ x in (0 : ℝ)..1, sieveProfile (m + 1) (m + 1)
                (Fin.cons x (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r))))| ≤
            (C₁ * sieveProfileScale (m + 1) / Real.log R) *
                pinnedMajorantValue m R (fun q => q.val) j r +
              C₂ * pinnedGlobalNormalization m M
                  (fun q : commonPrimeUniverse M N => q.val) *
                modulusLogScale (M * assignmentPrimeProduct (fun q => q.val) r) ^ 3 *
                sieveProfileScale (m + 1) * majorantFaceValue (m + 1) m
                  (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r)) := by
  obtain ⟨C₁, hC₁, hmove⟩ := exists_commonPinnedProfile_replacement_error
  obtain ⟨C₂, hC₂, hface⟩ := exists_pinnedUnshiftedValue_face_error
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro m M R N hm hlog hM hR hRN hsmall j r
  have h₁ := hmove hm hlog hR (commonPrimeUniverse M N) (fun q => q.val)
    commonPrimeUniverse_prime Subtype.val_injective (commonPrimeUniverse_large hsmall) j r
  have h₂ := hface hm hlog hM hR hRN hsmall j r
  exact combine_pinned_face_errors h₁ h₂

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedProfile_face_error_split
