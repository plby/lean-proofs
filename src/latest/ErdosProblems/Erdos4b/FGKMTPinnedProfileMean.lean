/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMajorantMean
import ErdosProblems.Erdos4b.FGKMTPinnedFaceApproximation

/-!
# Uniform face approximation for the original pinned profile

The arithmetic majorant is now eliminated from the error term. A single
absolute constant controls both the smallness hypothesis and the error,
before the dimension, modulus, cutoff, prime universe, pin, and tuple.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem close_pinned_face_error {E J B L T D V C₁ C₂ C : ℝ}
    (hB : 0 ≤ B) (hL : 0 < L) (hT : 0 ≤ T) (hD : 1 ≤ D) (hV : 0 ≤ V)
    (hC₁ : 0 ≤ C₁) (hC : 4 * C₁ + C₂ ≤ C)
    (hJ : J ≤ 4 * B * L * V)
    (hE : E ≤ (C₁ * T / L) * J + C₂ * B * D * T * V) :
    E ≤ C * B * D * T * V := by
  have hfirst : (C₁ * T / L) * J ≤ 4 * C₁ * B * T * V := by
    calc
      _ ≤ (C₁ * T / L) * (4 * B * L * V) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = _ := by field_simp [hL.ne']
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  calc
    E ≤ (C₁ * T / L) * J + C₂ * B * D * T * V := hE
    _ ≤ 4 * C₁ * B * T * V + C₂ * B * D * T * V := add_le_add hfirst le_rfl
    _ ≤ (4 * C₁ * B * T * V) * D + C₂ * B * D * T * V := by
      exact add_le_add (le_mul_of_one_le_right (by positivity) hD) le_rfl
    _ = (4 * C₁ + C₂) * (B * D * T * V) := by ring
    _ ≤ C * (B * D * T * V) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by ring

theorem exists_commonPinnedProfile_face_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R N : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R → R ≤ N →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      ∀ (j : Fin (m + 1)) (r : commonPrimeUniverse M N → Option (Fin m)),
        C * (m + 1 : ℕ) * sieveProfileScale (m + 1) *
            modulusLogScale (M * assignmentPrimeProduct (fun q => q.val) r) ^ 3 ≤ Real.log R →
        |commonPinnedProfile m R (fun q => q.val) j r -
          pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M N => q.val) *
            Real.log R * (∫ x in (0 : ℝ)..1, sieveProfile (m + 1) (m + 1)
              (Fin.cons x (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r))))| ≤
          C * pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M N => q.val) *
            modulusLogScale (M * assignmentPrimeProduct (fun q => q.val) r) ^ 3 *
            sieveProfileScale (m + 1) * majorantFaceValue (m + 1) m
              (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r)) := by
  obtain ⟨C₀, hC₀, hmajor⟩ := exists_pinnedMajorantValue_upper
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ := exists_commonPinnedProfile_face_error_split
  let C := C₀ + 4 * C₁ + C₂
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC₀C : C₀ ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro m M R N hm hlog hM hR hRN hsmall j r hcost
  let p : commonPrimeUniverse M N → ℕ := fun q => q.val
  have hT : 0 ≤ sieveProfileScale (m + 1) :=
    zero_le_one.trans (profile_scales_bounds (Nat.succ_pos m) hlog).1
  have hD : 1 ≤ modulusLogScale (M * assignmentPrimeProduct p r) ^ 3 :=
    one_le_pow₀ (one_le_modulusLogScale _)
  have hcost₀ : C₀ * (m + 1 : ℕ) * sieveProfileScale (m + 1) *
      modulusLogScale (M * assignmentPrimeProduct p r) ^ 3 ≤ Real.log R := by
    apply le_trans _ hcost
    have h := mul_le_mul_of_nonneg_right hC₀C
      (show 0 ≤ (m + 1 : ℕ) * sieveProfileScale (m + 1) *
        modulusLogScale (M * assignmentPrimeProduct p r) ^ 3 by positivity)
    convert h using 1 <;> ring
  have hJ := hmajor hm hlog hM hR hsmall (commonPrimeUniverse M N) p
    commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd j r hcost₀
  have hB : 0 ≤ pinnedGlobalNormalization m M p :=
    (show (0 : ℝ) ≤ ((M.totient : ℝ) / M) / 2 by positivity).trans
      (pinnedGlobalNormalization_bounds (seven_le_of_profile_log hlog) hM hsmall
        commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd).1
  exact close_pinned_face_error hB (Real.log_pos (by exact_mod_cast hR)) hT hD
    (majorantFaceValue_nonneg _ _ _) hC₁.le (by dsimp only [C]; linarith) hJ
    (hsplit hm hlog hM hR hRN hsmall j r)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.close_pinned_face_error
#print axioms Erdos4b.FGKMT.exists_commonPinnedProfile_face_error
