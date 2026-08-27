/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedFaceMean
import ErdosProblems.Erdos4b.FGKMTPinnedNormalization

/-!
# Harmonic face approximation for the actual unshifted amplitude

The finite normalization is independent of the remaining tuple and the
pin. Its comparison with the limiting density is a separate obligation;
the equality below does not suppress the finite Euler tail.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem scale_harmonic_face_error {A K S I L B C D T V : ℝ}
    (hA : 0 ≤ A) (hB : A * K = B)
    (h : |S - K * L * I| ≤ C * K * D * T * V) :
    |A * S - B * L * I| ≤ C * B * D * T * V := by
  calc
    _ = |A * (S - K * L * I)| := by rw [← hB]; congr 1; ring
    _ = A * |S - K * L * I| := by rw [abs_mul, abs_of_nonneg hA]
    _ ≤ A * (C * K * D * T * V) := mul_le_mul_of_nonneg_left h hA
    _ = _ := by rw [← hB]; ring

theorem exists_pinnedUnshiftedValue_face_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R N : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R → R ≤ N →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      ∀ (j : Fin (m + 1)) (r : commonPrimeUniverse M N → Option (Fin m)),
        |pinnedUnshiftedValue m R (fun q => q.val) j r -
          pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M N => q.val) *
            Real.log R * (∫ x in (0 : ℝ)..1, sieveProfile (m + 1) (m + 1)
              (Fin.cons x (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r))))| ≤
          C * pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M N => q.val) *
            modulusLogScale (M * assignmentPrimeProduct (fun q => q.val) r) ^ 3 *
            sieveProfileScale (m + 1) * majorantFaceValue (m + 1) m
              (sieveLogTuple R (assignmentPrimeTuple (fun q => q.val) r)) := by
  obtain ⟨C, hC, hmean⟩ := exists_sieveProfile_face_smooth_error
  refine ⟨C, hC, ?_⟩
  intro m M R N hm hlog hM hR hRN hsmall j r
  let p : commonPrimeUniverse M N → ℕ := fun q => q.val
  let t := sieveLogTuple R (assignmentPrimeTuple p r)
  let K := sieveMainConstant (M * assignmentPrimeProduct p r)
    (fun l => pinnedLocalDenominator (m + 1) l)
  let A := pinnedBaseFactor p r * pinnedBaseEulerProduct p r
  let I := ∫ x in (0 : ℝ)..1, sieveProfile (m + 1) (m + 1) (Fin.cons x t)
  let S := ∑ a ∈ Finset.Icc 0 R,
    sieveProfile (m + 1) (m + 1) (Fin.cons (Real.log a / Real.log R) t) *
      roughSieveWeight (M * assignmentPrimeProduct p r)
        (fun l => pinnedLocalDenominator (m + 1) l) a
  have hrough : ∀ q, 2 * (m + 1) ^ 2 < p q := commonPrimeUniverse_large hsmall
  have hA : 0 ≤ A := mul_nonneg
    (pinnedBaseFactor_nonneg (fun q => (commonPrimeUniverse_prime q).one_le) r)
    (pinnedBaseEulerProduct_nonneg hm hrough r)
  have hnorm : A * K = pinnedGlobalNormalization m M p :=
    pinnedHarmonicNormalization_eq_global hm hM hsmall commonPrimeUniverse_prime
      Subtype.val_injective commonPrimeUniverse_not_dvd r
  have hMe : 0 < M * assignmentPrimeProduct p r := Nat.mul_pos hM
    (assignmentPrimeProduct_pos (fun q => (commonPrimeUniverse_prime q).pos) r)
  have hsmallMe (l : ℕ) (hl : l.Prime) (hlk : l ≤ 2 * (m + 1) ^ 2) :
      l ∣ M * assignmentPrimeProduct p r := dvd_mul_of_dvd_left (hsmall l hl hlk) _
  have h := hmean hm hlog hMe hR hsmallMe true t (sieveLogTuple_nonneg R _)
  have hg : actualSieveDenominator true (m + 1) =
      (fun l : ℕ => pinnedLocalDenominator (m + 1) l) := by
    funext l
    simp only [actualSieveDenominator, if_true, Nat.cast_add, Nat.cast_one]
  rw [hg] at h
  change |S - K * Real.log R * I| ≤
    C * K * modulusLogScale (M * assignmentPrimeProduct p r) ^ 3 *
      sieveProfileScale (m + 1) * majorantFaceValue (m + 1) m t at h
  have hsum : pinnedUnshiftedValue m R p j r = A * S :=
    pinnedUnshiftedValue_eq_sum_Icc hm hR hRN hsmall j r
  change |pinnedUnshiftedValue m R p j r - pinnedGlobalNormalization m M p * Real.log R * I| ≤ _
  rw [hsum]
  exact scale_harmonic_face_error hA hnorm h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_pinnedUnshiftedValue_face_error
