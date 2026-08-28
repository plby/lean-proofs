import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativePermutationInsertion

/-!
# Recursion by rank-preserving insertion

The explicit deletion inverse gives a recursor for data indexed by a finite
permutation. Its computation rule uses the actual insertion permutation.
-/

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

universe u

variable {P : (n : ℕ) → Equiv.Perm (Fin n) → Sort u}

/-- Build permutation-indexed data by inserting one coordinate at a time. -/
def permutationInsertionRec (hzero : ∀ e, P 0 e)
    (hsucc : ∀ {n} (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)),
      P n e → P (n + 1) (insertPermutation e r)) :
    ∀ {n} (e : Equiv.Perm (Fin n)), P n e
  | 0, e => hzero e
  | n + 1, E => Equiv.piCongrLeft (P (n + 1)) (insertPermutationEquiv n)
      (fun er => hsucc er.1 er.2 (permutationInsertionRec hzero hsucc er.1)) E

@[simp] theorem permutationInsertionRec_zero (hzero : ∀ e, P 0 e)
    (hsucc : ∀ {n} (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)),
      P n e → P (n + 1) (insertPermutation e r))
    (e : Equiv.Perm (Fin 0)) : permutationInsertionRec hzero hsucc e = hzero e := rfl

/-- The recursor computes at every insertion, independently of its rank. -/
@[simp] theorem permutationInsertionRec_insert (hzero : ∀ e, P 0 e)
    (hsucc : ∀ {n} (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)),
      P n e → P (n + 1) (insertPermutation e r))
    {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) :
    permutationInsertionRec hzero hsucc (insertPermutation e r) =
      hsucc e r (permutationInsertionRec hzero hsucc e) := by
  exact Equiv.piCongrLeft_apply_apply (P (n + 1)) (insertPermutationEquiv n)
    (fun er => hsucc er.1 er.2 (permutationInsertionRec hzero hsucc er.1)) (e, r)

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
