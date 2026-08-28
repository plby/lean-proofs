import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic

/-!
# Refinement of the actual cocycle extension

Restriction of local coordinates defines a genuine map between the
concrete extension presheaves. Sheafification gives the corresponding
map of original extension sheaves, fixing both the kernel sheaf and the
native constant-integer quotient.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1 Cech

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι κ : Type} {U : ι → Opens X} {V : κ → Opens X}
    (r : κ → ι) (hr : ∀ a, V a ≤ U (r a)) (c : CechOneCocycle F U)

/-- Actual refinement of compatible local coordinates at fixed degree. -/
def refinementHom (T : Opens X) :
    ExtensionSection c T →+ ExtensionSection (Cech.refinement F r hr c) T where
  toFun s := ⟨⟨s.1.1, fun a => res F (inf_le_inf_left T (hr a)) (s.1.2 (r a))⟩, by
    intro a b
    have h := congrArg (res F (inf_le_inf_left T (inf_le_inf (hr a) (hr b))))
      (s.2 (r a) (r b))
    simpa only [map_sub, map_zsmul, res_trans, Cech.refinement_value] using h⟩
  map_zero' := by
    apply extensionSection_ext
    · rfl
    · intro a
      exact map_zero _
  map_add' s t := by
    apply extensionSection_ext
    · rfl
    · intro a
      exact map_add _ _ _

@[simp] theorem refinementHom_degree (T : Opens X) (s : ExtensionSection c T) :
    degreeHom (Cech.refinement F r hr c) T (refinementHom r hr c T s) =
      degreeHom c T s := rfl

@[simp] theorem refinementHom_coordinate (T : Opens X) (a : κ)
    (s : ExtensionSection c T) :
    coordinateHom (Cech.refinement F r hr c) T a (refinementHom r hr c T s) =
      res F (inf_le_inf_left T (hr a)) (coordinateHom c T (r a) s) := rfl

theorem restrict_refinementHom {T S : Opens X} (hST : S ≤ T)
    (s : ExtensionSection c T) :
    restrict (Cech.refinement F r hr c) hST (refinementHom r hr c T s) =
      refinementHom r hr c S (restrict c hST s) := by
  apply extensionSection_ext
  · rfl
  · intro a
    change res F _ (res F _ _) = res F _ (res F _ _)
    rw [res_trans, res_trans]

theorem refinementHom_include (T : Opens X) (s : Section F T) :
    refinementHom r hr c T (includeHom c T s) =
      includeHom (Cech.refinement F r hr c) T s := by
  apply extensionSection_ext
  · rfl
  · intro a
    exact res_trans F _ _ _

def refinementPre : presheaf c ⟶ presheaf (Cech.refinement F r hr c) where
  app T := AddCommGrpCat.ofHom (refinementHom r hr c T.unop)
  naturality T S h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (restrict_refinementHom r hr c (leOfHom h.unop) s).symm

theorem inclusionPre_refinementPre :
    inclusionPre c ≫ refinementPre r hr c = inclusionPre (Cech.refinement F r hr c) := by
  ext T s
  exact refinementHom_include r hr c T.unop s

theorem refinementPre_projectionPre :
    refinementPre r hr c ≫ projectionPre (Cech.refinement F r hr c) = projectionPre c := by
  ext T s
  rfl

/-- A genuine map of sheafified extensions, not merely a relation between
their formal cocycles. -/
def refinementMap : extensionSheaf c ⟶ extensionSheaf (Cech.refinement F r hr c) where
  hom := CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (refinementPre r hr c)

theorem unit_refinementMap :
    unit c ≫ (refinementMap r hr c).hom =
      refinementPre r hr c ≫ unit (Cech.refinement F r hr c) :=
  (CategoryTheory.toSheafify_naturality
    (Opens.grothendieckTopology X) (refinementPre r hr c)).symm

@[simp] theorem refinementMap_app_unit (T : Opens X) (s : ExtensionSection c T) :
    (refinementMap r hr c).hom.app (op T) ((unit c).app (op T) s) =
      (unit (Cech.refinement F r hr c)).app (op T) (refinementHom r hr c T s) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_refinementMap r hr c) (op T)) s

theorem inclusion_refinementMap :
    inclusion c ≫ refinementMap r hr c = inclusion (Cech.refinement F r hr c) := by
  apply CategoryTheory.Sheaf.hom_ext
  change (inclusionPre c ≫ unit c) ≫ (refinementMap r hr c).hom =
    inclusionPre (Cech.refinement F r hr c) ≫ unit (Cech.refinement F r hr c)
  rw [Category.assoc, unit_refinementMap, ← Category.assoc, inclusionPre_refinementPre]

theorem refinementMap_projection :
    refinementMap r hr c ≫ projection (Cech.refinement F r hr c) = projection c := by
  apply extensionHom_ext c
  change unit c ≫ ((refinementMap r hr c).hom ≫
    (projection (Cech.refinement F r hr c)).hom) = unit c ≫ (projection c).hom
  rw [← Category.assoc, unit_refinementMap, Category.assoc, unit_projection,
    ← Category.assoc, refinementPre_projectionPre, unit_projection]

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
