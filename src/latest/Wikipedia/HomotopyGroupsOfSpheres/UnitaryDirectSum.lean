import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryBlocks

/-! # Actual direct sums of unitary coordinate frames -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryDirectSum

variable {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem matrix_unitary (U : unitary (Matrix M M ℂ)) (V : unitary (Matrix N N ℂ)) :
    Matrix.fromBlocks U.val 0 0 V.val ∈ unitary (Matrix (M ⊕ N) (M ⊕ N) ℂ) := by
  have hr : Matrix.fromBlocks U.val 0 0 V.val * star (Matrix.fromBlocks U.val 0 0 V.val) = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_one] using
      congrArg₂ (fun A B ↦ Matrix.fromBlocks A 0 0 B) U.property.2 V.property.2
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

def inclusion : unitary (Matrix M M ℂ) × unitary (Matrix N N ℂ) →*
    unitary (Matrix (M ⊕ N) (M ⊕ N) ℂ) where
  toFun p := ⟨Matrix.fromBlocks p.1.val 0 0 p.2.val, matrix_unitary p.1 p.2⟩
  map_one' := Subtype.ext Matrix.fromBlocks_one
  map_mul' p q := by
    apply Subtype.ext
    change Matrix.fromBlocks (p.1.val * q.1.val) 0 0 (p.2.val * q.2.val) =
      Matrix.fromBlocks p.1.val 0 0 p.2.val * Matrix.fromBlocks q.1.val 0 0 q.2.val
    simp [Matrix.fromBlocks_multiply]

theorem inclusion_val (U : unitary (Matrix M M ℂ)) (V : unitary (Matrix N N ℂ)) :
    (inclusion (U, V)).val = Matrix.fromBlocks U.val 0 0 V.val := rfl

theorem inclusion_real (U : unitary (Matrix M M ℂ)) (V : unitary (Matrix N N ℂ))
    (hU : ∀ i j, star (U.val i j) = U.val i j)
    (hV : ∀ i j, star (V.val i j) = V.val i j) (i j : M ⊕ N) :
    star ((inclusion (U, V)).val i j) = (inclusion (U, V)).val i j := by
  rcases i with i | i <;> rcases j with j | j
  · exact hU i j
  · exact star_zero _
  · exact star_zero _
  · exact hV i j

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryDirectSum
