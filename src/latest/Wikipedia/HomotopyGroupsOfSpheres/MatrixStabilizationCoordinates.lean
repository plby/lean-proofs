import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryBlocks
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryStabilization

/-! # Exact block coordinates for every iterated first-entry stabilization -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.MatrixStabilizationCoordinates

open QuaternionicSymmetricMatrices

def index (n r : ℕ) : Fin r ⊕ Fin n ≃ Fin (n + r) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm r n))

theorem index_zero_inr (n : ℕ) (i : Fin n) : index n 0 (Sum.inr i) = i := by
  apply Fin.ext
  change 0 + i.val = i.val
  omega

theorem index_succ_inl_zero (n r : ℕ) : index n (r + 1) (Sum.inl 0) = 0 := by
  apply Fin.ext
  rfl

theorem index_succ_inl_succ (n r : ℕ) (i : Fin r) :
    index n (r + 1) (Sum.inl i.succ) = (index n r (Sum.inl i)).succ := by
  apply Fin.ext
  rfl

theorem index_succ_inr (n r : ℕ) (i : Fin n) :
    index n (r + 1) (Sum.inr i) = (index n r (Sum.inr i)).succ := by
  apply Fin.ext
  change r + 1 + i.val = r + i.val + 1
  omega

theorem stabilization_val_at (n r : ℕ) (B : Space (Fin n)) (i j : Fin r ⊕ Fin n) :
    (stabilizationIterate n r B).val.val (index n r i) (index n r j) =
      Matrix.fromBlocks 1 0 0 B.val.val i j := by
  induction r with
  | zero =>
    rcases i with i | i
    · exact Fin.elim0 i
    rcases j with j | j
    · exact Fin.elim0 j
    rw [index_zero_inr, index_zero_inr]
    rfl
  | succ r ih =>
    change MatrixBorder.border 1 (stabilizationIterate n r B).val.val
      (index n (r + 1) i) (index n (r + 1) j) = _
    rcases i with i | i <;> rcases j with j | j
    · cases i using Fin.cases <;> cases j using Fin.cases
      all_goals simp [index_succ_inl_zero, index_succ_inl_succ, Matrix.one_apply, ih, eq_comm]
    · cases i using Fin.cases
      all_goals simp [index_succ_inl_zero, index_succ_inl_succ, index_succ_inr, ih]
    · cases j using Fin.cases
      all_goals simp [index_succ_inl_zero, index_succ_inl_succ, index_succ_inr, ih]
    · simp [index_succ_inr, ih]

def modelHomeomorph (n r : ℕ) : Space (Fin r ⊕ Fin n) ≃ₜ Space (Fin (n + r)) :=
  reindexHomeomorph (index n r)

theorem modelHomeomorph_identity (n r : ℕ) : modelHomeomorph n r identity = identity :=
  reindexHomeomorph_identity (index n r)

theorem modelHomeomorph_embed (n r : ℕ) (B : Space (Fin n)) :
    modelHomeomorph n r (blockSum (identity : Space (Fin r)) B) = stabilizationIterate n r B := by
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (index n r).surjective i
  obtain ⟨j, rfl⟩ := (index n r).surjective j
  change Matrix.fromBlocks 1 0 0 B.val.val
    ((index n r).symm (index n r i)) ((index n r).symm (index n r j)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact (stabilization_val_at n r B i j).symm

theorem modelHomeomorph_symm_stabilization (n r : ℕ) (B : Space (Fin n)) :
    (modelHomeomorph n r).symm (stabilizationIterate n r B) = blockSum identity B := by
  rw [← modelHomeomorph_embed, Homeomorph.symm_apply_apply]

end Wikipedia.HomotopyGroupsOfSpheres.MatrixStabilizationCoordinates
