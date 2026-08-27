/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteTransform
import ErdosProblems.Erdos4b.FGKMTPrimeAssignment

/-!
# Common and moved factors of a contributing pair

The kernel vanishes unless both assignments use exactly the same primes.
Removing every prime whose coordinate changes leaves a common tuple.
The two moved tuples have exactly the same product, not merely a bound.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

def commonAssignment (r s : α → Option ι) : α → Option ι :=
  fun q => if r q = s q then r q else none

def movedAssignment (r s : α → Option ι) : α → Option ι :=
  fun q => if r q = s q then none else r q

def SamePrimeSupport (r s : α → Option ι) : Prop :=
  ∀ q, r q = none ↔ s q = none

omit [Fintype α] in
theorem commonAssignment_comm (r s : α → Option ι) :
    commonAssignment r s = commonAssignment s r := by
  funext q
  by_cases h : r q = s q
  · simp [commonAssignment, h]
  · simp [commonAssignment, h, Ne.symm h]

omit [Fintype α] in
theorem commonAssignment_eq_none_of_moved {r s : α → Option ι} {q : α}
    (h : r q ≠ s q) : commonAssignment r s q = none := by
  simp [commonAssignment, h]

theorem assignmentPrimeTuple_split (p : α → ℕ) (r s : α → Option ι) (i : ι) :
    assignmentPrimeTuple p r i =
      assignmentPrimeTuple p (commonAssignment r s) i *
        assignmentPrimeTuple p (movedAssignment r s) i := by
  unfold assignmentPrimeTuple
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases h : r q = s q <;> simp [commonAssignment, movedAssignment, h]

theorem assignmentPrimeProduct_split (p : α → ℕ) (r s : α → Option ι) :
    assignmentPrimeProduct p r =
      assignmentPrimeProduct p (commonAssignment r s) *
        assignmentPrimeProduct p (movedAssignment r s) := by
  unfold assignmentPrimeProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases h : r q = s q <;> simp [commonAssignment, movedAssignment, h]

theorem samePrimeSupport_of_kernel_ne_zero (v : α → ℝ) {r s : α → Option ι}
    (h : assignmentQuadraticKernel v r s ≠ 0) : SamePrimeSupport r s := by
  intro q
  have hq := (Finset.prod_ne_zero_iff.mp h) q (Finset.mem_univ q)
  cases hr : r q <;> cases hs : s q <;> simp_all [localQuadraticKernel]

omit [Fintype α] in
theorem movedAssignment_samePrimeSupport {r s : α → Option ι}
    (h : SamePrimeSupport r s) :
    SamePrimeSupport (movedAssignment r s) (movedAssignment s r) := by
  intro q
  by_cases heq : r q = s q
  · simp [movedAssignment, heq]
  · simpa only [movedAssignment, if_neg heq, if_neg (Ne.symm heq)] using h q

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_eq_of_samePrimeSupport (p : α → ℕ)
    {r s : α → Option ι} (h : SamePrimeSupport r s) :
    assignmentPrimeProduct p r = assignmentPrimeProduct p s := by
  apply Finset.prod_congr rfl
  intro q _hq
  simp only [h q]

theorem movedAssignment_products_eq (p : α → ℕ) {r s : α → Option ι}
    (h : SamePrimeSupport r s) :
    assignmentPrimeProduct p (movedAssignment r s) =
      assignmentPrimeProduct p (movedAssignment s r) :=
  assignmentPrimeProduct_eq_of_samePrimeSupport p (movedAssignment_samePrimeSupport h)

omit [Fintype α] in
theorem movedAssignment_none_iff_eq {r s : α → Option ι}
    (h : SamePrimeSupport r s) (q : α) :
    movedAssignment r s q = none ↔ r q = s q := by
  by_cases heq : r q = s q
  · simp [movedAssignment, heq]
  · have hn : r q ≠ none := by
      intro hr
      exact heq (hr.trans ((h q).mp hr).symm)
    simp [movedAssignment, heq, hn]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentPrimeTuple_split
#print axioms Erdos4b.FGKMT.movedAssignment_products_eq
