/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentProductFiber
import ErdosProblems.Erdos4b.FGKMTAssignmentCompatibility
import Mathlib.Tactic

/-!
# Three-state encoding of compatible divisor pairs

Every used prime remembers its coordinate and whether it occurs only
on the left, only on the right, or on both sides. The code is injective
on compatible pairs and retains exactly the merged prime product.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators ArithmeticFunction.omega

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

def compatiblePairCode (de : (α → Option ι) × (α → Option ι)) : α → Option (ι × Fin 3) :=
  fun q => match de.1 q, de.2 q with
    | none, none => none
    | some i, none => some (i, 0)
    | none, some i => some (i, 1)
    | some i, some _ => some (i, 2)

def restoreCompatiblePair (r : α → Option (ι × Fin 3)) :
    (α → Option ι) × (α → Option ι) :=
  (fun q => match r q with
    | none => none
    | some (i, b) => if b = 1 then none else some i,
   fun q => match r q with
    | none => none
    | some (i, b) => if b = 0 then none else some i)

omit [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι] in
theorem restoreCompatiblePair_code {d e : α → Option ι} (hde : AssignmentCompatible d e) :
    restoreCompatiblePair (compatiblePairCode (d, e)) = (d, e) := by
  apply Prod.ext <;> funext q
  all_goals
    have hq := hde q
    cases hd : d q <;> cases he : e q <;>
      simp_all [restoreCompatiblePair, compatiblePairCode]

omit [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι] in
theorem compatiblePairCode_injective_on_compatible
    {de fg : (α → Option ι) × (α → Option ι)}
    (hde : AssignmentCompatible de.1 de.2) (hfg : AssignmentCompatible fg.1 fg.2)
    (heq : compatiblePairCode de = compatiblePairCode fg) : de = fg := by
  have h := congrArg restoreCompatiblePair heq
  simpa only [restoreCompatiblePair_code hde, restoreCompatiblePair_code hfg] using h

omit [DecidableEq α] [DecidableEq ι] [Fintype ι] in
theorem compatiblePairCode_primeProduct (p : α → ℕ)
    (de : (α → Option ι) × (α → Option ι)) :
    assignmentPrimeProduct p (compatiblePairCode de) =
      assignmentPrimeProduct p (mergeAssignment de.1 de.2) := by
  apply Finset.prod_congr rfl
  intro q _hq
  cases hd : de.1 q <;> cases he : de.2 q <;>
    simp [compatiblePairCode, mergeAssignment, hd, he]

open scoped Classical in
def compatiblePairProductFiber (p : α → ℕ) (D : ℕ) :
    Finset ((α → Option ι) × (α → Option ι)) :=
  Finset.univ.filter (fun de => AssignmentCompatible de.1 de.2 ∧
    assignmentPrimeProduct p (mergeAssignment de.1 de.2) = D)

omit [DecidableEq ι] in
theorem mem_compatiblePairProductFiber {p : α → ℕ} {D : ℕ}
    {de : (α → Option ι) × (α → Option ι)} :
    de ∈ compatiblePairProductFiber p D ↔ AssignmentCompatible de.1 de.2 ∧
      assignmentPrimeProduct p (mergeAssignment de.1 de.2) = D := by
  simp only [compatiblePairProductFiber, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq ι] in
theorem card_compatiblePairProductFiber_le {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) {D : ℕ} (hD : Squarefree D) :
    (compatiblePairProductFiber (ι := ι) p D).card ≤ (3 * Fintype.card ι) ^ ω D := by
  classical
  calc
    _ ≤ (assignmentProductFiber (ι := ι × Fin 3) p D).card := by
      apply Finset.card_le_card_of_injOn compatiblePairCode
      · intro de hde
        apply mem_assignmentProductFiber.mpr
        exact (compatiblePairCode_primeProduct p de).trans (mem_compatiblePairProductFiber.mp hde).2
      · intro de hde fg hfg heq
        exact compatiblePairCode_injective_on_compatible
          (mem_compatiblePairProductFiber.mp hde).1
          (mem_compatiblePairProductFiber.mp hfg).1 heq
    _ ≤ (Fintype.card (ι × Fin 3)) ^ ω D := card_assignmentProductFiber_le hp hinj hD
    _ = _ := by simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.restoreCompatiblePair_code
#print axioms Erdos4b.FGKMT.card_compatiblePairProductFiber_le
