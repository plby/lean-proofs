import Mathlib.GroupTheory.Perm.Fin

/-!
# Inserting the interval coordinate into an ordered cube cell

For an old coordinate order `e`, insertion at `k` has value `0` at
position `k` and value `(e j).succ` at position `k.succAbove j`.
The definition uses the actual cycle on the initial coordinate range.
-/

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision.PermutationInsertion

variable {n : ℕ}

/-- Insert the new coordinate `0` into position `k`, preserving the old order. -/
def insert (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e) * k.cycleRange

@[simp] theorem insert_apply_self (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    insert k e k = 0 := by
  simp [insert]

@[simp] theorem insert_apply_succAbove (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) (j : Fin n) :
    insert k e (k.succAbove j) = (e j).succ := by
  simp [insert]

/-- The insertion is literally the ordered tuple with the zero coordinate inserted. -/
theorem insert_apply (k : Fin (n + 1)) (e : Equiv.Perm (Fin n))
    (j : Fin (n + 1)) :
    insert k e j =
      (k.insertNth (0 : Fin (n + 1)) (fun i => (e i).succ) :
        Fin (n + 1) → Fin (n + 1)) j := by
  refine Fin.succAboveCases k ?_ ?_ j
  · simp
  · intro i
    simp

@[simp] theorem insert_symm_apply_zero (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    (insert k e).symm 0 = k := by
  apply (insert k e).injective
  simp

@[simp] theorem insert_symm_apply_succ (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) (j : Fin n) :
    (insert k e).symm j.succ = k.succAbove (e.symm j) := by
  apply (insert k e).injective
  simp

/-- The orientation changes by precisely the number of coordinates passed by `0`. -/
@[simp] theorem sign_insert (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (insert k e) = (-1) ^ (k : ℕ) * Equiv.Perm.sign e := by
  simp [insert, mul_comm]

/-- The same orientation formula in the integer coefficient ring. -/
theorem sign_insert_int (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (insert k e) : ℤ) =
      (-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ) := by
  simp

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision.PermutationInsertion
