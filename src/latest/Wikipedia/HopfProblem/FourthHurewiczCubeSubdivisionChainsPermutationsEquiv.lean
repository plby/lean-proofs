import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsPermutationsBasic
import Mathlib.Data.Fintype.EquivFin

/-!
# Every coordinate order is a unique insertion

The position of the inserted zero is recovered by the inverse permutation.
The other entries recover the old permutation in their original relative order.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision.PermutationInsertion

variable {n : ℕ}

/-- Different insertion data give different actual permutations. -/
theorem insert_injective :
    Function.Injective (fun p : Fin (n + 1) × Equiv.Perm (Fin n) => insert p.1 p.2) := by
  rintro ⟨k, e⟩ ⟨l, f⟩ h
  have hk : k = l := by
    simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ.symm 0) h
  subst l
  refine Prod.ext rfl ?_
  apply Equiv.ext
  intro j
  apply Fin.succ_injective n
  simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (k.succAbove j)) h

/-- Insertion enumerates all actual permutations, in every dimension including zero. -/
theorem insert_bijective :
    Function.Bijective (fun p : Fin (n + 1) × Equiv.Perm (Fin n) => insert p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨insert_injective, by simp [Fintype.card_perm, Nat.factorial_succ]⟩

/-- Coordinate insertion as an equivalence with the original permutation type. -/
def insertEquiv (n : ℕ) :
    (Fin (n + 1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun p => insert p.1 p.2) insert_bijective

@[simp] theorem insertEquiv_apply (p : Fin (n + 1) × Equiv.Perm (Fin n)) :
    insertEquiv n p = insert p.1 p.2 := rfl

/-- The inverse equivalence records the literal position of coordinate zero. -/
@[simp] theorem insertEquiv_symm_fst (σ : Equiv.Perm (Fin (n + 1))) :
    ((insertEquiv n).symm σ).1 = σ.symm 0 := by
  have h := congrArg (fun τ : Equiv.Perm (Fin (n + 1)) => τ.symm 0)
    ((insertEquiv n).apply_symm_apply σ)
  simpa only [insertEquiv_apply, insert_symm_apply_zero] using h

/-- The other inverse component recovers the remaining coordinates in order. -/
theorem insertEquiv_symm_snd_apply (σ : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (((insertEquiv n).symm σ).2 j).succ = σ ((σ.symm 0).succAbove j) := by
  have h := congrArg (fun τ : Equiv.Perm (Fin (n + 1)) =>
    τ ((((insertEquiv n).symm σ).1).succAbove j))
    ((insertEquiv n).apply_symm_apply σ)
  simpa only [insertEquiv_apply, insert_apply_succAbove, insertEquiv_symm_fst] using h

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision.PermutationInsertion
