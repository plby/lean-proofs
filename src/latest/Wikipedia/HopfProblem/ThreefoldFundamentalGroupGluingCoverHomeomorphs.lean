import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Flattening subspaces in the threefold gluing cover

A subset of an ambient space, when contained in a larger subspace, has the
same topology whether formed directly or as a preimage in that subspace.
The homeomorphisms below preserve the actual ambient point definitionally.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Set

variable {X : Type*} [TopologicalSpace X] {A B C : Set X}

/-- Flatten a subspace preimage when the smaller subset lies in the larger one. -/
def subspacePreimageHomeomorph (hBA : B ⊆ A) :
    ((Subtype.val : A → X) ⁻¹' B) ≃ₜ B where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hBA x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem subspacePreimageHomeomorph_apply (hBA : B ⊆ A)
    (x : (Subtype.val : A → X) ⁻¹' B) :
    subspacePreimageHomeomorph hBA x = ⟨x.val.val, x.property⟩ := rfl

@[simp] theorem subspacePreimageHomeomorph_apply_coe (hBA : B ⊆ A)
    (x : (Subtype.val : A → X) ⁻¹' B) :
    (subspacePreimageHomeomorph hBA x : X) = x.val.val := rfl

@[simp] theorem subspacePreimageHomeomorph_symm_apply (hBA : B ⊆ A) (x : B) :
    (subspacePreimageHomeomorph hBA).symm x =
      ⟨⟨x.val, hBA x.property⟩, x.property⟩ := rfl

@[simp] theorem subspacePreimageHomeomorph_symm_apply_coe (hBA : B ⊆ A) (x : B) :
    ((subspacePreimageHomeomorph hBA).symm x : A) =
      ⟨x.val, hBA x.property⟩ := rfl

@[simp] theorem subspacePreimageHomeomorph_symm_apply_coe_coe (hBA : B ⊆ A) (x : B) :
    (((subspacePreimageHomeomorph hBA).symm x : A) : X) = x.val := rfl

/-- Flatten the intersection of two subspace preimages.  Only their intersection
needs to lie in the larger subspace. -/
def subspacePreimageInterHomeomorph (hBC : B ∩ C ⊆ A) :
    ↥(((Subtype.val : A → X) ⁻¹' B) ∩ ((Subtype.val : A → X) ⁻¹' C)) ≃ₜ
      ↥(B ∩ C) :=
  subspacePreimageHomeomorph hBC

@[simp] theorem subspacePreimageInterHomeomorph_apply (hBC : B ∩ C ⊆ A)
    (x : ↥(((Subtype.val : A → X) ⁻¹' B) ∩ ((Subtype.val : A → X) ⁻¹' C))) :
    subspacePreimageInterHomeomorph hBC x = ⟨x.val.val, x.property⟩ := rfl

@[simp] theorem subspacePreimageInterHomeomorph_apply_coe (hBC : B ∩ C ⊆ A)
    (x : ↥(((Subtype.val : A → X) ⁻¹' B) ∩ ((Subtype.val : A → X) ⁻¹' C))) :
    (subspacePreimageInterHomeomorph hBC x : X) = x.val.val := rfl

@[simp] theorem subspacePreimageInterHomeomorph_symm_apply (hBC : B ∩ C ⊆ A)
    (x : ↥(B ∩ C)) :
    (subspacePreimageInterHomeomorph hBC).symm x =
      ⟨⟨x.val, hBC x.property⟩, x.property⟩ := rfl

@[simp] theorem subspacePreimageInterHomeomorph_symm_apply_coe (hBC : B ∩ C ⊆ A)
    (x : ↥(B ∩ C)) :
    ((subspacePreimageInterHomeomorph hBC).symm x : A) =
      ⟨x.val, hBC x.property⟩ := rfl

@[simp] theorem subspacePreimageInterHomeomorph_symm_apply_coe_coe (hBC : B ∩ C ⊆ A)
    (x : ↥(B ∩ C)) :
    (((subspacePreimageInterHomeomorph hBC).symm x : A) : X) = x.val := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
