import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryDeterminant
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing the actual symmetric determinant-one matrix space

Simultaneous row and column reindexing preserves unitarity, symmetry, and
determinant. The resulting homeomorphism preserves the standard identity
and therefore induces isomorphisms on the native based homotopy groups.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N M : Type} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

theorem reindex_unitary (e : N ≃ M) (U : unitary (Matrix N N ℂ)) :
    Matrix.reindex e e U.val ∈ unitary (Matrix M M ℂ) := by
  let f := Matrix.reindexRingEquiv ℂ e
  have hstar : star (f U.val) = f (star U.val) :=
    Matrix.conjTranspose_reindex e e U.val
  apply Unitary.mem_iff.mpr
  change star (f U.val) * f U.val = 1 ∧ f U.val * star (f U.val) = 1
  rw [hstar, ← map_mul, ← map_mul, Unitary.star_mul_self_of_mem U.property,
    Unitary.mul_star_self_of_mem U.property, map_one]
  exact ⟨rfl, rfl⟩

def reindex (e : N ≃ M) (B : Space N) : Space M :=
  ⟨⟨Matrix.reindex e e B.val.val, reindex_unitary e B.val⟩, by
    rw [Matrix.transpose_reindex, B.property]⟩

theorem continuous_reindex (e : N ≃ M) : Continuous (reindex e) := by
  have h : Continuous (fun B : Space N ↦ Matrix.reindex e e B.val.val) :=
    (continuous_subtype_val.comp continuous_subtype_val).matrix_reindex e e
  exact (h.subtype_mk _).subtype_mk _

theorem reindex_symm_reindex (e : N ≃ M) (B : Space N) :
    reindex e.symm (reindex e B) = B :=
  Subtype.ext (Subtype.ext ((Matrix.reindex e e).symm_apply_apply B.val.val))

theorem determinant_reindex (e : N ≃ M) (B : Space N) :
    determinant (reindex e B) = determinant B := by
  apply Circle.ext
  exact Matrix.det_reindex_self e B.val.val

theorem reindex_identity (e : N ≃ M) : reindex e (identity : Space N) = identity := by
  apply Subtype.ext
  apply Subtype.ext
  exact (Matrix.reindexRingEquiv ℂ e).map_one

def specialReindex (e : N ≃ M) (B : SpecialSpace N) : SpecialSpace M :=
  ⟨reindex e B.val, (determinant_reindex e B.val).trans B.property⟩

theorem continuous_specialReindex (e : N ≃ M) : Continuous (specialReindex e) :=
  ((continuous_reindex e).comp continuous_subtype_val).subtype_mk _

theorem specialReindex_symm_specialReindex (e : N ≃ M) (B : SpecialSpace N) :
    specialReindex e.symm (specialReindex e B) = B :=
  Subtype.ext (reindex_symm_reindex e B.val)

def specialReindexHomeomorph (e : N ≃ M) : SpecialSpace N ≃ₜ SpecialSpace M where
  toFun := specialReindex e
  invFun := specialReindex e.symm
  left_inv := specialReindex_symm_specialReindex e
  right_inv := specialReindex_symm_specialReindex e.symm
  continuous_toFun := continuous_specialReindex e
  continuous_invFun := continuous_specialReindex e.symm

theorem specialReindexHomeomorph_identity (e : N ≃ M) :
    specialReindexHomeomorph e specialIdentity = specialIdentity :=
  Subtype.ext (reindex_identity e)

def specialReindexHomotopyMulEquiv (e : N ≃ M) (d : ℕ) [NeZero d] :
    HomotopyGroup (Fin d) (SpecialSpace N) specialIdentity ≃*
      HomotopyGroup (Fin d) (SpecialSpace M) specialIdentity :=
  pointedHomeomorphMulEquiv (specialReindexHomeomorph e) specialIdentity specialIdentity
    (specialReindexHomeomorph_identity e)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
