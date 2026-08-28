import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryReindex
import Mathlib.Data.Matrix.Block

/-! # Direct sums and coordinate homeomorphisms for symmetric unitary matrices -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem blockSum_unitary (A : Space M) (B : Space N) :
    Matrix.fromBlocks A.val.val 0 0 B.val.val ∈ unitary (Matrix (M ⊕ N) (M ⊕ N) ℂ) := by
  have hr : Matrix.fromBlocks A.val.val 0 0 B.val.val *
      star (Matrix.fromBlocks A.val.val 0 0 B.val.val) = 1 := by
    change Matrix.fromBlocks A.val.val 0 0 B.val.val *
      (Matrix.fromBlocks A.val.val 0 0 B.val.val).conjTranspose = 1
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.fromBlocks_one] using
      congrArg₂ (fun C D ↦ Matrix.fromBlocks C 0 0 D) A.val.property.2 B.val.property.2
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

def blockSum (A : Space M) (B : Space N) : Space (M ⊕ N) :=
  ⟨⟨Matrix.fromBlocks A.val.val 0 0 B.val.val, blockSum_unitary A B⟩, by
    change (Matrix.fromBlocks A.val.val 0 0 B.val.val).transpose =
      Matrix.fromBlocks A.val.val 0 0 B.val.val
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, A.property, B.property]⟩

theorem blockSum_val (A : Space M) (B : Space N) :
    (blockSum A B).val.val = Matrix.fromBlocks A.val.val 0 0 B.val.val := rfl

theorem continuous_blockSum : Continuous (fun p : Space M × Space N ↦ blockSum p.1 p.2) := by
  have hA : Continuous (fun p : Space M × Space N ↦ p.1.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hB : Continuous (fun p : Space M × Space N ↦ p.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact (continuous_apply_apply i j).comp hA
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply_apply i j).comp hB

theorem blockSum_identity : blockSum (identity : Space M) (identity : Space N) = identity :=
  Subtype.ext (Subtype.ext Matrix.fromBlocks_one)

def reindexHomeomorph (e : M ≃ N) : Space M ≃ₜ Space N where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv := reindex_symm_reindex e
  right_inv := reindex_symm_reindex e.symm
  continuous_toFun := continuous_reindex e
  continuous_invFun := continuous_reindex e.symm

theorem reindexHomeomorph_identity (e : M ≃ N) : reindexHomeomorph e identity = identity :=
  reindex_identity e

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
