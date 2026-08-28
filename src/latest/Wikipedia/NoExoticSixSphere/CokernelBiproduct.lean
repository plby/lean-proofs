import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The native cokernel of a block-diagonal map

The comparison with the biproduct of the original cokernels is constructed
by its universal property. Its projection formula is retained for the
relative chain sequence, where it identifies the actual two quotient maps.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.CokernelBiproduct

variable {C : Type*} [Category* C] [Abelian C]
  {A B D E : C} (f : A ⟶ B) (g : D ⟶ E)

abbrev projection : B ⊞ E ⟶ cokernel f ⊞ cokernel g :=
  biprod.map (cokernel.π f) (cokernel.π g)

theorem map_projection : biprod.map f g ≫ projection f g = 0 := by
  apply biprod.hom_ext'
  · change biprod.inl ≫ biprod.map f g ≫ biprod.map (cokernel.π f) (cokernel.π g) = _
    rw [biprod.inl_map_assoc, biprod.inl_map, ← Category.assoc,
      cokernel.condition, zero_comp, comp_zero]
  · change biprod.inr ≫ biprod.map f g ≫ biprod.map (cokernel.π f) (cokernel.π g) = _
    rw [biprod.inr_map_assoc, biprod.inr_map, ← Category.assoc,
      cokernel.condition, zero_comp, comp_zero]

/-- The original block projection is a cokernel of the block-diagonal map. -/
def projectionIsCokernel :
    IsColimit (CokernelCofork.ofπ (projection f g) (map_projection f g)) := by
  apply CokernelCofork.IsColimit.ofπ'
  intro T k hk
  have hf : f ≫ (biprod.inl ≫ k) = 0 := by
    rw [← biprod.inl_map_assoc, hk, comp_zero]
  have hg : g ≫ (biprod.inr ≫ k) = 0 := by
    rw [← biprod.inr_map_assoc, hk, comp_zero]
  refine ⟨biprod.desc (cokernel.desc f (biprod.inl ≫ k) hf)
    (cokernel.desc g (biprod.inr ≫ k) hg), ?_⟩
  apply biprod.hom_ext'
  · simp only [projection, biprod.inl_map_assoc, biprod.inl_desc, Category.assoc,
      cokernel.π_desc]
  · simp only [projection, biprod.inr_map_assoc, biprod.inr_desc, Category.assoc,
      cokernel.π_desc]

/-- The canonical isomorphism retains the actual cokernel and the two actual quotient objects. -/
def iso : cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g :=
  (cokernelIsCokernel (biprod.map f g)).coconePointUniqueUpToIso (projectionIsCokernel f g)

@[reassoc]
theorem projection_iso : cokernel.π (biprod.map f g) ≫ (iso f g).hom = projection f g :=
  (cokernelIsCokernel (biprod.map f g)).comp_coconePointUniqueUpToIso_hom
    (projectionIsCokernel f g) WalkingParallelPair.one

end NoExoticSixSphere.CokernelBiproduct
