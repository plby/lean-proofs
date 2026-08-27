/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedAbsoluteKernel
import ErdosProblems.Erdos4b.FGKMTPinnedPairVariation
import ErdosProblems.Erdos4b.FGKMTAssignmentAffineMoment

/-! # The complete pinned off-diagonal contribution before its energy normalization -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

open scoped Classical in
def pinnedPairMajorant (m R : ℕ) (p : α → ℕ) (D E : ℝ)
    (r s : α → Option (Fin m)) : ℝ :=
  if SamePrimeSupport r s then
    (primeAssignmentFaceMajorant (m + 1) m R p (commonAssignment r s) ^ 2 *
      pinnedCommonKernelWeight m p (commonAssignment r s)) *
        pinnedMovedKernelWeight m p (movedAssignment r s) *
          (D * Real.log (assignmentPrimeProduct p (movedAssignment r s)) + E)
  else 0

theorem sum_pinnedPairMajorant_le {m R : ℕ} (hm : 1 ≤ m) {p : α → ℕ}
    (hp : ∀ q, 2 ≤ p q) (hinj : Function.Injective p)
    (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q) {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (∑ r : α → Option (Fin m), ∑ s, pinnedPairMajorant m R p D E r s) ≤
      absolutePinnedFaceMajorantSum m R p * (Real.exp 4 * (D * (16 * (m + 1 : ℕ)) + E)) := by
  classical
  have h := sum_common_moved_affine_le_rough (m := m) (by omega : 2 ≤ m + 1)
    (by omega : m ≤ m + 1) hinj hrough
    (fun u => primeAssignmentFaceMajorant (m + 1) m R p u ^ 2 * pinnedCommonKernelWeight m p u)
    (fun u => mul_nonneg (sq_nonneg _) (pinnedCommonKernelWeight_nonneg hp u)) hD hE
  simpa only [pinnedPairMajorant, pinnedMovedKernelWeight, absolutePinnedFaceMajorantSum,
    Nat.cast_add, Nat.cast_one] using h

omit [DecidableEq α] [Fintype α] in
theorem exists_pinnedSieveVariationTerm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      C * (m + 1 : ℕ) * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 ≤
        Real.log R →
      ∀ (j : Fin (m + 1)) (r s : commonPrimeUniverse M R → Option (Fin m)),
        |pinnedSieveVariationTerm m R (fun q => q.val) j r s| ≤
          (2 * (pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) *
            Real.log R) ^ 2) * pinnedPairMajorant m R (fun q => q.val)
              (C * sieveProfileScale (m + 1) / Real.log R)
              (2 * (C * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 / Real.log R))
              r s := by
  obtain ⟨C, hC, hpoint⟩ := exists_commonPinnedProfile_pair_bound
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall hcost j r s
  classical
  let p : commonPrimeUniverse M R → ℕ := fun q => q.val
  have hlarge (q : commonPrimeUniverse M R) : m + 1 < p q := by
    have h := commonPrimeUniverse_large hsmall q
    nlinarith
  by_cases hrs : SamePrimeSupport r s
  · have hden := mul_pos (commonPinnedRowWeight_pos hlarge r) (commonPinnedRowWeight_pos hlarge s)
    have hW : 0 ≤ pinnedCommonKernelWeight m p (commonAssignment r s) *
        pinnedMovedKernelWeight m p (movedAssignment r s) :=
      mul_nonneg (pinnedCommonKernelWeight_nonneg (fun q => (commonPrimeUniverse_prime q).two_le) _)
        (assignmentScalarWeight_nonneg (fun _ => div_nonneg zero_le_one (sq_nonneg _)) _)
    rw [pinnedSieveVariationTerm, abs_div, abs_mul, abs_of_pos hden, mul_div_assoc,
      pinned_assignmentAbsoluteKernel_split (fun q => (commonPrimeUniverse_prime q).two_le) hrs,
      pinnedPairMajorant, if_pos hrs]
    have h := mul_le_mul_of_nonneg_right (hpoint hm hlog hM hR hsmall hcost j r s hrs) hW
    dsimp only [p] at h
    convert h using 1
    all_goals first | rfl | ring
  · have hz : assignmentQuadraticKernel (fun q => (p q : ℝ) - 1) r s = 0 := by
      by_contra hne
      exact hrs (samePrimeSupport_of_kernel_ne_zero _ hne)
    dsimp only [p] at hz
    simp only [pinnedSieveVariationTerm, hz, mul_zero, zero_div, abs_zero,
      pinnedPairMajorant, if_neg hrs]
    exact le_rfl

omit [DecidableEq α] [Fintype α] in
theorem exists_commonPinnedQuadratic_offDiagonal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      C * (m + 1 : ℕ) * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 ≤
        Real.log R →
      ∀ j : Fin (m + 1),
        |commonPinnedQuadratic m M R j - commonPinnedDiagonal m M R j| ≤
          (2 * (pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) *
            Real.log R) ^ 2) * absolutePinnedFaceMajorantSum m R
              (fun q : commonPrimeUniverse M R => q.val) *
              (Real.exp 4 * ((C * sieveProfileScale (m + 1) / Real.log R) *
                (16 * (m + 1 : ℕ)) +
                2 * (C * sieveProfileScale (m + 1) *
                  modulusLogScale (M * R) ^ 3 / Real.log R))) := by
  obtain ⟨C, hC, hterm⟩ := exists_pinnedSieveVariationTerm_bound
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall hcost j
  classical
  let p : commonPrimeUniverse M R → ℕ := fun q => q.val
  let A := pinnedGlobalNormalization m M p * Real.log R
  let D := C * sieveProfileScale (m + 1) / Real.log R
  let E := 2 * (C * sieveProfileScale (m + 1) * modulusLogScale (M * R) ^ 3 / Real.log R)
  have hT : 0 ≤ sieveProfileScale (m + 1) :=
    zero_le_one.trans (profile_scales_bounds (Nat.succ_pos m) hlog).1
  have hΛ : 0 ≤ modulusLogScale (M * R) := zero_le_one.trans (one_le_modulusLogScale _)
  have hL : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  rw [commonPinnedQuadratic_sub_diagonal hm hsmall]
  calc
    _ ≤ ∑ r : commonPrimeUniverse M R → Option (Fin m),
        |∑ s, pinnedSieveVariationTerm m R p j r s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : commonPrimeUniverse M R → Option (Fin m),
        ∑ s, |pinnedSieveVariationTerm m R p j r s| :=
      Finset.sum_le_sum fun r _hr => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : commonPrimeUniverse M R → Option (Fin m),
        ∑ s, (2 * A ^ 2) * pinnedPairMajorant m R p D E r s :=
      Finset.sum_le_sum fun r _hr => Finset.sum_le_sum fun s _hs =>
        hterm hm hlog hM hR hsmall hcost j r s
    _ = (2 * A ^ 2) * ∑ r, ∑ s, pinnedPairMajorant m R p D E r s := by
      simp only [Finset.mul_sum]
    _ ≤ (2 * A ^ 2) * (absolutePinnedFaceMajorantSum m R p *
        (Real.exp 4 * (D * (16 * (m + 1 : ℕ)) + E))) :=
      mul_le_mul_of_nonneg_left (sum_pinnedPairMajorant_le hm
        (fun q => (commonPrimeUniverse_prime q).two_le) Subtype.val_injective
        (commonPrimeUniverse_large hsmall) hD hE) (by positivity)
    _ = _ := by dsimp only [A, D, E]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_pinnedSieveVariationTerm_bound
#print axioms Erdos4b.FGKMT.exists_commonPinnedQuadratic_offDiagonal_bound
