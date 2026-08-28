import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberChartsBasic
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Fin

/-!
# The consecutive endpoints for inserting one chamber coordinate

Insertion ranks run from the top down. Reversing them gives the finite
sequence beginning at zero and ending at one, whose adjacent pairs are
exactly the lower and upper endpoints of each insertion.
-/

noncomputable section

open scoped Topology unitInterval BigOperators

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {m : ℕ}

theorem chamberUpper_succ_eq_lower_castSucc (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin m) (u : NativeCube (Fin m)) :
    chamberUpper e j.succ chart u = chamberLower e j.castSucc chart u := by
  rw [chamberUpper_of_rank e j.succ chart u j rfl,
    chamberLower_of_rank e j.castSucc chart u j rfl]

/-- The cut sequence in the order in which native slices are traversed. -/
def chamberCutSequence (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) :
    Fin (m + 2) → C(NativeCube (Fin m), I) :=
  Fin.cons (ContinuousMap.const _ 0) (fun j : Fin (m + 1) => chamberUpper e j.rev chart)

@[simp] theorem chamberCutSequence_zero (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart 0 u = 0 := rfl

theorem chamberCutSequence_succ (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.succ u = chamberUpper e j.rev chart u := by
  simp [chamberCutSequence]

@[simp] theorem chamberCutSequence_last (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart (Fin.last (m + 1)) u = 1 := by
  change chamberUpper e (Fin.last m).rev chart u = 1
  rw [Fin.rev_last]
  exact chamberUpper_first e 0 chart u rfl

theorem chamberCutSequence_castSucc (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.castSucc u = chamberLower e j.rev chart u := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change 0 = chamberLower e (0 : Fin (m + 1)).rev chart u
    rw [Fin.rev_zero]
    exact (chamberLower_last e (Fin.last m) chart u rfl).symm
  · change chamberUpper e k.castSucc.rev chart u = chamberLower e k.succ.rev chart u
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact chamberUpper_succ_eq_lower_castSucc e chart k.rev u

theorem chamberCuts_sum_rev {A : Type*} [AddCommMonoid A] (f : Fin (m + 1) → A) :
    ∑ j : Fin (m + 1), f j.rev = ∑ j : Fin (m + 1), f j :=
  Equiv.sum_comp Fin.revPerm f

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
