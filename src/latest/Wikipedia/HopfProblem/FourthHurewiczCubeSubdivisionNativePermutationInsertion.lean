import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Rank-preserving insertion of a cube coordinate

Inserting the new coordinate label at a chosen rank does not change the order
of the old ranks. This gives a dimension-independent enumeration of the
chambers obtained by successively inserting coordinates.
-/

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {n : ℕ}

/-- Insert the last coordinate label into the prescribed rank. -/
def insertPermutation (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' r).trans (e.optionCongr.trans finSuccEquivLast.symm)

@[simp] theorem insertPermutation_apply_at (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : insertPermutation e r r = Fin.last n := by
  simp [insertPermutation]

@[simp] theorem insertPermutation_apply_succAbove (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (j : Fin n) :
    insertPermutation e r (r.succAbove j) = (e j).castSucc := by
  simp [insertPermutation]

@[simp] theorem insertPermutation_symm_last (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : (insertPermutation e r).symm (Fin.last n) = r := by
  apply (insertPermutation e r).injective
  simp

@[simp] theorem insertPermutation_symm_castSucc (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (j : Fin n) :
    (insertPermutation e r).symm j.castSucc = r.succAbove (e.symm j) := by
  apply (insertPermutation e r).injective
  simp

@[simp] theorem insertPermutation_apply_eq_last_iff (e : Equiv.Perm (Fin n))
    (r i : Fin (n + 1)) : insertPermutation e r i = Fin.last n ↔ i = r := by
  rw [← insertPermutation_apply_at e r, Equiv.apply_eq_iff_eq]

@[simp] theorem insertPermutation_apply_eq_castSucc_iff (e : Equiv.Perm (Fin n))
    (r i : Fin (n + 1)) (j : Fin n) :
    insertPermutation e r i = j.castSucc ↔ i = r.succAbove (e.symm j) := by
  rw [← (insertPermutation e r).eq_symm_apply, insertPermutation_symm_castSucc]

/-- An old rank strictly below the insertion rank is unchanged. -/
theorem insertPermutation_apply_castSucc_of_lt (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (j : Fin n) (h : j.castSucc < r) :
    insertPermutation e r j.castSucc = (e j).castSucc := by
  rw [← Fin.succAbove_of_castSucc_lt r j h, insertPermutation_apply_succAbove]

/-- An old rank at or above the insertion rank shifts by one. -/
theorem insertPermutation_apply_succ_of_le (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (j : Fin n) (h : r ≤ j.castSucc) :
    insertPermutation e r j.succ = (e j).castSucc := by
  rw [← Fin.succAbove_of_le_castSucc r j h, insertPermutation_apply_succAbove]

theorem insertPermutation_pair_injective :
    Function.Injective (fun er : Equiv.Perm (Fin n) × Fin (n + 1) =>
      insertPermutation er.1 er.2) := by
  rintro ⟨e, r⟩ ⟨f, s⟩ h
  have hrs : r = s := by
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E.symm (Fin.last n)) h
  subst s
  have hef : e = f := by
    apply Equiv.ext
    intro j
    apply Fin.castSucc_injective n
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E (r.succAbove j)) h
  exact congrArg (fun e : Equiv.Perm (Fin n) => (e, r)) hef

/-- Removing the distinguished value and then restoring it recovers an
equivalence which fixes that value. -/
theorem optionCongr_removeNone_of_none {α β : Type*} (e : Option α ≃ Option β)
    (h : e none = none) : e.removeNone.optionCongr = e := by
  apply Equiv.ext
  intro a
  cases a with
  | none => simpa using h.symm
  | some a =>
      change some (e.removeNone a) = e (some a)
      cases ha : e (some a) with
      | none =>
          have : some a = none := e.injective (ha.trans h.symm)
          cases this
      | some b => simpa only [ha] using e.removeNone_some ⟨b, ha⟩

/-- The option-coordinate presentation of a permutation after deleting the
rank occupied by the last label. -/
def deletePermutationOption (E : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Option (Fin n)) :=
  (finSuccEquiv' (E.symm (Fin.last n))).symm.trans (E.trans finSuccEquivLast)

@[simp] theorem deletePermutationOption_none (E : Equiv.Perm (Fin (n + 1))) :
    deletePermutationOption E none = none := by
  simp [deletePermutationOption]

/-- Delete the last coordinate label, retaining the relative order of ranks. -/
def deletePermutation (E : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin n) :=
  (deletePermutationOption E).removeNone

theorem deletePermutation_castSucc (E : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (deletePermutation E j).castSucc = E ((E.symm (Fin.last n)).succAbove j) := by
  have h := congrArg (fun e : Equiv.Perm (Option (Fin n)) => e (some j))
    (optionCongr_removeNone_of_none (deletePermutationOption E)
      (deletePermutationOption_none E))
  have h' := congrArg finSuccEquivLast.symm h
  simpa [deletePermutation, deletePermutationOption] using h'

@[simp] theorem insertPermutation_deletePermutation (E : Equiv.Perm (Fin (n + 1))) :
    insertPermutation (deletePermutation E) (E.symm (Fin.last n)) = E := by
  ext i
  refine Fin.succAboveCases (E.symm (Fin.last n)) ?_ (fun j => ?_) i
  · simp
  · rw [insertPermutation_apply_succAbove, deletePermutation_castSucc]

/-- Every permutation has one unique rank-preserving insertion presentation. -/
def insertPermutationEquiv (n : ℕ) :
    (Equiv.Perm (Fin n) × Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 1)) where
  toFun er := insertPermutation er.1 er.2
  invFun E := (deletePermutation E, E.symm (Fin.last n))
  left_inv er := insertPermutation_pair_injective
    (insertPermutation_deletePermutation (insertPermutation er.1 er.2))
  right_inv := insertPermutation_deletePermutation

@[simp] theorem insertPermutationEquiv_apply (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : insertPermutationEquiv n (e, r) = insertPermutation e r := rfl

@[simp] theorem insertPermutationEquiv_symm_apply (E : Equiv.Perm (Fin (n + 1))) :
    (insertPermutationEquiv n).symm E = (deletePermutation E, E.symm (Fin.last n)) := rfl

@[simp] theorem deletePermutation_insertPermutation (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : deletePermutation (insertPermutation e r) = e :=
  congrArg Prod.fst ((insertPermutationEquiv n).symm_apply_apply (e, r))

/-- Reindex a sum over all permutations by the old permutation and insertion rank. -/
theorem sum_insertPermutation {A : Type*} [AddCommMonoid A]
    (F : Equiv.Perm (Fin (n + 1)) → A) :
    ∑ E, F E = ∑ e : Equiv.Perm (Fin n), ∑ r : Fin (n + 1), F (insertPermutation e r) := by
  rw [← (insertPermutationEquiv n).sum_comp F, Fintype.sum_prod_type]
  rfl

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
