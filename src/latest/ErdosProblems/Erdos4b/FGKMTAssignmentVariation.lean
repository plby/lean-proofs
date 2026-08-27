/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentSplit
import ErdosProblems.Erdos4b.FGKMTCommonCoefficients
import ErdosProblems.Erdos4b.FGKMTWeightedFaceMajorant

/-!
# Variation bound on the actual common-coefficient assignments

The majorant is evaluated at the reduced common tuple. Multiplying the
profile variation by the first profile costs its square, with one
absolute constant chosen before the dimension and all prime labels.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def primeAssignmentMajorant (k R : ℕ) (p : α → ℕ) (r : α → Option (Fin k)) : ℝ :=
  sieveProfileMajorant k k (sieveLogTuple R (assignmentPrimeTuple p r))

omit [DecidableEq α] in
theorem primeAssignmentProfile_le_common_majorant {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (R : ℕ) {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (r s : α → Option (Fin k)) :
    primeAssignmentProfile k R p r ≤ primeAssignmentMajorant k R p (commonAssignment r s) := by
  have ht := sieveLogTuple_nonneg R (assignmentPrimeTuple p (commonAssignment r s))
  have hle (i : Fin k) :
      sieveLogTuple R (assignmentPrimeTuple p (commonAssignment r s)) i ≤
        sieveLogTuple R (assignmentPrimeTuple p r) i := by
    have hsplit : assignmentPrimeTuple p r = fun i =>
        assignmentPrimeTuple p (commonAssignment r s) i *
          assignmentPrimeTuple p (movedAssignment r s) i :=
      funext (assignmentPrimeTuple_split p r s)
    rw [hsplit]
    exact sieveLogTuple_le_mul R _ _ (assignmentPrimeTuple_pos hp _)
      (assignmentPrimeTuple_pos hp _) i
  refine (sieveProfile_antitone_on_orthant hk hlog ht hle).trans ?_
  refine (show sieveProfile k k _ ≤ ∏ i, dimensionProfileFactor k
      (sieveLogTuple R (assignmentPrimeTuple p (commonAssignment r s)) i) from ?_).trans
    (shortTensor_le_majorant hk hlog hk ht)
  exact mul_le_of_le_one_left
    (Finset.prod_nonneg fun i _ => dimensionProfileFactor_nonneg k _) (sieveCutoff_le_one _)

omit [DecidableEq α] [Fintype α] in
theorem exists_primeAssignmentProfile_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : Type*) [Fintype β],
      ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (R : ℕ) (p : β → ℕ), (∀ q, 0 < p q) →
        ∀ r s : β → Option (Fin k), SamePrimeSupport r s →
          |primeAssignmentProfile k R p r - primeAssignmentProfile k R p s| ≤
            (C * sieveProfileScale k * primeAssignmentMajorant k R p (commonAssignment r s)) *
              (Real.log (assignmentPrimeProduct p (movedAssignment r s)) / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_movedFactor_variation_bound
  refine ⟨C, hC, ?_⟩
  intro β _ k hk hlog R p hp r s hrs
  have hprod : (∏ i, assignmentPrimeTuple p (movedAssignment r s) i) =
      ∏ i, assignmentPrimeTuple p (movedAssignment s r) i := by
    simp only [prod_assignmentPrimeTuple]
    exact movedAssignment_products_eq p hrs
  have hb := hbound hk hlog k R (assignmentPrimeTuple p (commonAssignment r s))
    (assignmentPrimeTuple p (movedAssignment r s)) (assignmentPrimeTuple p (movedAssignment s r))
    (assignmentPrimeTuple_pos hp _) (assignmentPrimeTuple_pos hp _)
    (assignmentPrimeTuple_pos hp _) hprod
  have hleft : (fun i => assignmentPrimeTuple p (commonAssignment r s) i *
      assignmentPrimeTuple p (movedAssignment r s) i) = assignmentPrimeTuple p r :=
    (funext (assignmentPrimeTuple_split p r s)).symm
  have hright : (fun i => assignmentPrimeTuple p (commonAssignment r s) i *
      assignmentPrimeTuple p (movedAssignment s r) i) = assignmentPrimeTuple p s := by
    rw [commonAssignment_comm r s]
    exact (funext (assignmentPrimeTuple_split p s r)).symm
  simpa only [hleft, hright, prod_assignmentPrimeTuple, primeAssignmentProfile,
    primeAssignmentMajorant] using hb

omit [DecidableEq α] [Fintype α] in
theorem exists_primeAssignmentProfile_product_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : Type*) [Fintype β],
      ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (R : ℕ) (p : β → ℕ), (∀ q, 0 < p q) →
        ∀ r s : β → Option (Fin k), SamePrimeSupport r s →
          |primeAssignmentProfile k R p r *
              (primeAssignmentProfile k R p s - primeAssignmentProfile k R p r)| ≤
            (C * sieveProfileScale k * primeAssignmentMajorant k R p (commonAssignment r s) ^ 2) *
              (Real.log (assignmentPrimeProduct p (movedAssignment r s)) / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_primeAssignmentProfile_variation_bound
  refine ⟨C, hC, ?_⟩
  intro β _ k hk hlog R p hp r s hrs
  have hF : 0 ≤ primeAssignmentProfile k R p r := sieveProfile_nonneg _ _ _
  have hB : 0 ≤ primeAssignmentMajorant k R p (commonAssignment r s) :=
    sieveProfileMajorant_nonneg _ _ _
  rw [abs_mul, abs_of_nonneg hF, abs_sub_comm]
  calc
    _ ≤ primeAssignmentMajorant k R p (commonAssignment r s) *
        ((C * sieveProfileScale k * primeAssignmentMajorant k R p (commonAssignment r s)) *
          (Real.log (assignmentPrimeProduct p (movedAssignment r s)) / Real.log R)) :=
      mul_le_mul (primeAssignmentProfile_le_common_majorant hk hlog R hp r s)
        (hbound β hk hlog R p hp r s hrs) (abs_nonneg _) hB
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.primeAssignmentProfile_le_common_majorant
#print axioms Erdos4b.FGKMT.exists_primeAssignmentProfile_product_variation_bound
