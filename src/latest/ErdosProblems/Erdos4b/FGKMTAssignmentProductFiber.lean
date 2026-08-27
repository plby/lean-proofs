/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeAssignment
import Mathlib.Algebra.Order.Antidiag.Nat

/-!
# Fixed-product assignment fibers

Coordinate products inject the actual finite assignments into ordered
factorizations. Mathlib's squarefree ordered-factor count then gives
the dimension-explicit fiber bound, including empty coordinate types.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators ArithmeticFunction.omega

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

def assignmentProductFiber (p : α → ℕ) (D : ℕ) : Finset (α → Option ι) :=
  Finset.univ.filter (fun r => assignmentPrimeProduct p r = D)

omit [DecidableEq ι] in
theorem mem_assignmentProductFiber {p : α → ℕ} {D : ℕ} {r : α → Option ι} :
    r ∈ assignmentProductFiber p D ↔ assignmentPrimeProduct p r = D := by
  simp only [assignmentProductFiber, Finset.mem_filter, Finset.mem_univ, true_and]

def assignmentFinPrimeTuple (p : α → ℕ) (r : α → Option ι) : Fin (Fintype.card ι) → ℕ :=
  fun i => assignmentPrimeTuple p r ((Fintype.equivFin ι).symm i)

omit [DecidableEq α] in
theorem prod_assignmentFinPrimeTuple (p : α → ℕ) (r : α → Option ι) :
    (∏ i, assignmentFinPrimeTuple p r i) = assignmentPrimeProduct p r := by
  calc
    _ = ∏ i : ι, assignmentPrimeTuple p r i := by
      apply Fintype.prod_equiv (Fintype.equivFin ι).symm
      intro i
      rfl
    _ = _ := prod_assignmentPrimeTuple p r

omit [DecidableEq α] in
theorem assignmentFinPrimeTuple_injective {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) :
    Function.Injective (assignmentFinPrimeTuple p : (α → Option ι) → _) := by
  intro r s hrs
  apply assignmentPrimeTuple_injective hp hinj
  funext i
  have hi := congrFun hrs ((Fintype.equivFin ι) i)
  simpa only [assignmentFinPrimeTuple, Equiv.symm_apply_apply] using hi

omit [DecidableEq ι] in
theorem card_assignmentProductFiber_le {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) {D : ℕ} (hD : Squarefree D) :
    (assignmentProductFiber (ι := ι) p D).card ≤ (Fintype.card ι) ^ ω D := by
  classical
  calc
    _ ≤ (Nat.finMulAntidiag (Fintype.card ι) D).card := by
      apply Finset.card_le_card_of_injOn (assignmentFinPrimeTuple p)
      · intro r hr
        exact Nat.mem_finMulAntidiag.mpr
          ⟨(prod_assignmentFinPrimeTuple p r).trans (mem_assignmentProductFiber.mp hr), hD.ne_zero⟩
      · exact (assignmentFinPrimeTuple_injective hp hinj).injOn
    _ = _ := Nat.card_finMulAntidiag_of_squarefree hD

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.card_assignmentProductFiber_le
