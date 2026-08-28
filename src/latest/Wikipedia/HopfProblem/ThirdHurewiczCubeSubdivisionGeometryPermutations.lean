import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometry
import Mathlib.Data.Fintype.Perm

/-!
# The six coordinate orders and their actual permutation signs

The explicit enumeration is `012, 021, 102, 201, 120, 210`.
This connects the literal prism expansion with sums over all actual
coordinate permutations, without replacing that index type.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz.Geometry

/-- All coordinate orders, with the principal tetrahedron first. -/
def cubePermutation : Fin 6 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 1 2, Equiv.swap 0 1,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2),
    (Equiv.swap 1 2).trans (Equiv.swap 0 1), Equiv.swap 0 2]

theorem cubePermutation_injective : Function.Injective cubePermutation := by
  decide

theorem cubePermutation_bijective : Function.Bijective cubePermutation := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨cubePermutation_injective, by norm_num [Fintype.card_perm, Nat.factorial]⟩

/-- A sum over permutations is precisely the six explicitly ordered summands. -/
theorem sum_cubePermutations {A : Type*} [AddCommMonoid A]
    (f : Equiv.Perm (Fin 3) → A) :
    ∑ e, f e = f 1 + f (Equiv.swap 1 2) + f (Equiv.swap 0 1) +
      f ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) +
      f ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) + f (Equiv.swap 0 2) := by
  rw [← cubePermutation_bijective.sum_comp f]
  simp [cubePermutation, Fin.sum_univ_succ, add_assoc]

/-- The six coefficients are the signs of the actual coordinate permutations. -/
theorem cubeOrientation_cubePermutation (i : Fin 6) :
    cubeOrientation (cubePermutation i) = ![1, -1, -1, 1, 1, -1] i := by
  fin_cases i <;>
    simp [cubePermutation, cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap']

theorem sum_oriented_cubePermutations {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (Fin 3) → A) :
    ∑ e, cubeOrientation e • f e =
      f 1 - f (Equiv.swap 1 2) - f (Equiv.swap 0 1) +
        f ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) +
        f ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) - f (Equiv.swap 0 2) := by
  rw [sum_cubePermutations]
  simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap', sub_eq_add_neg,
    add_assoc]

end Wikipedia.HopfProblem.ThirdHurewicz.Geometry
