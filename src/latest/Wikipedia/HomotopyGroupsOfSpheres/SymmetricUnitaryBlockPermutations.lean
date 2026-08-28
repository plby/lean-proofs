import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCoordinateChanges

/-! # Exact associativity and interchange of symmetric unitary blocks -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {M N P : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype P] [DecidableEq P]

theorem reindex_refl (B : Space M) : reindex (Equiv.refl M) B = B :=
  Subtype.ext (Subtype.ext rfl)

theorem reindex_blockSum_assoc (A : Space M) (B : Space N) (C : Space P) :
    reindex (Equiv.sumAssoc M N P) (blockSum (blockSum A B) C) = blockSum A (blockSum B C) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> rfl

theorem reindex_blockSum_swap (A : Space M) (B : Space N) :
    reindex (Equiv.sumComm M N) (blockSum A B) = blockSum B A := by
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
