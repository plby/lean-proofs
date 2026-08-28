import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsPermutationsEquiv
import Mathlib.Data.Fintype.BigOperators

/-!
# Reindexing the cube-cell sum by interval-coordinate insertion

The reindexing uses the actual coordinate-permutation equivalence.  In
particular, the interval-first shuffle coefficient `(-1)^k` combines
with the old cell sign to give exactly the new permutation sign.
-/

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision.PermutationInsertion

variable {n : ℕ}

/-- The iterated insertion sum is precisely the sum over all coordinate orders. -/
theorem sum_insert {A : Type*} [AddCommMonoid A]
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1), ∑ e : Equiv.Perm (Fin n), f (insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), f σ := by
  rw [← Fintype.sum_prod_type']
  exact insert_bijective.sum_comp f

/-- The interval-first shuffle signs are the actual inserted permutation signs. -/
theorem sum_sign_insert {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1), ∑ e : Equiv.Perm (Fin n),
      ((-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ)) • f (insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [sign_insert_int] using
    sum_insert (fun σ => (Equiv.Perm.sign σ : ℤ) • f σ)

/-- Nested scalar multiplication form, directly matching a signed shuffle expansion. -/
theorem sum_sign_smul_insert {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1), ∑ e : Equiv.Perm (Fin n),
      (-1 : ℤ) ^ (k : ℕ) • ((Equiv.Perm.sign e : ℤ) • f (insert k e))) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [mul_smul] using sum_sign_insert f

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision.PermutationInsertion
