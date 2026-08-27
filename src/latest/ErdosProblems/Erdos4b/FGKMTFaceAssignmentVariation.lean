/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFaceVariation
import ErdosProblems.Erdos4b.FGKMTAssignmentSplit

/-! # Face-profile variation after removing moved prime factors -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

def primeAssignmentFaceProfile (k m R : ℕ) (p : α → ℕ)
    (r : α → Option (Fin m)) : ℝ :=
  sieveFaceProfile k m (sieveLogTuple R (assignmentPrimeTuple p r))

def primeAssignmentFaceMajorant (k m R : ℕ) (p : α → ℕ)
    (r : α → Option (Fin m)) : ℝ :=
  majorantFaceValue k m (sieveLogTuple R (assignmentPrimeTuple p r))

theorem primeAssignmentFaceMajorant_le_common {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (m R : ℕ) {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (r s : α → Option (Fin m)) :
    primeAssignmentFaceMajorant k m R p r ≤
      primeAssignmentFaceMajorant k m R p (commonAssignment r s) := by
  apply majorantFaceValue_antitone_on_orthant hk hlog (sieveLogTuple_nonneg R _)
  have hsplit : assignmentPrimeTuple p r = fun i =>
      assignmentPrimeTuple p (commonAssignment r s) i *
        assignmentPrimeTuple p (movedAssignment r s) i :=
    funext (assignmentPrimeTuple_split p r s)
  rw [hsplit]
  exact sieveLogTuple_le_mul R _ _ (assignmentPrimeTuple_pos hp _) (assignmentPrimeTuple_pos hp _)

theorem primeAssignmentFaceProfile_le_common {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (m R : ℕ) {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (r s : α → Option (Fin m)) :
    primeAssignmentFaceProfile k m R p r ≤
      primeAssignmentFaceMajorant k m R p (commonAssignment r s) :=
  (sieveFaceProfile_le_majorant hk hlog _ _).trans
    (primeAssignmentFaceMajorant_le_common hk hlog m R hp r s)

omit [Fintype α] in
theorem exists_primeAssignmentFaceProfile_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : Type*) [Fintype β],
      ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (m R : ℕ) (p : β → ℕ), (∀ q, 0 < p q) →
        ∀ r s : β → Option (Fin m), SamePrimeSupport r s →
          |primeAssignmentFaceProfile k m R p r - primeAssignmentFaceProfile k m R p s| ≤
            (C * sieveProfileScale k *
              primeAssignmentFaceMajorant k m R p (commonAssignment r s)) *
                (Real.log (assignmentPrimeProduct p (movedAssignment r s)) / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveFaceProfile_reassignment_variation_bound
  refine ⟨C, hC, ?_⟩
  intro β _ k hk hlog m R p hp r s hrs
  let u := assignmentPrimeTuple p (commonAssignment r s)
  let a := assignmentPrimeTuple p (movedAssignment r s)
  let b := assignmentPrimeTuple p (movedAssignment s r)
  have hleft : assignmentPrimeTuple p r = fun i => u i * a i :=
    funext (assignmentPrimeTuple_split p r s)
  have hright : assignmentPrimeTuple p s = fun i => u i * b i := by
    dsimp only [u, b]
    rw [commonAssignment_comm r s]
    exact funext (assignmentPrimeTuple_split p s r)
  apply hbound hk hlog m (sieveLogTuple R u) (sieveLogTuple R (assignmentPrimeTuple p r))
    (sieveLogTuple R (assignmentPrimeTuple p s)) _ (sieveLogTuple_nonneg R u)
  · rw [hleft]
    exact sieveLogTuple_le_mul R u a (assignmentPrimeTuple_pos hp _) (assignmentPrimeTuple_pos hp _)
  · rw [hright]
    exact sieveLogTuple_le_mul R u b (assignmentPrimeTuple_pos hp _) (assignmentPrimeTuple_pos hp _)
  · rw [hleft, sieveLogTuple_mul_sub_sum R u a
      (assignmentPrimeTuple_pos hp _) (assignmentPrimeTuple_pos hp _), prod_assignmentPrimeTuple]
  · rw [hright, sieveLogTuple_mul_sub_sum R u b
      (assignmentPrimeTuple_pos hp _) (assignmentPrimeTuple_pos hp _), prod_assignmentPrimeTuple,
      movedAssignment_products_eq p (fun q => (hrs q).symm)]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.primeAssignmentFaceMajorant_le_common
#print axioms Erdos4b.FGKMT.exists_primeAssignmentFaceProfile_variation_bound
