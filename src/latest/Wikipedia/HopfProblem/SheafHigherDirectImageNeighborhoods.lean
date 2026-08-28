import Wikipedia.HopfProblem.SheafHigherDirectImageBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestriction

/-!
# The genuine cohomology groups on inverse-image neighborhoods

The objects in the following diagram are the existing Ext-defined
`Sheaf.H` groups of the sheaf restricted to the actual inverse-image
open subspaces.  Restriction maps are the maps of Mathlib's cohomology
presheaf transported through the proved canonical open-subspace
comparison.  This defines the usual cohomology presheaf, not a sheaf or
a substitute definition of a higher direct image.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

open HolomorphicSheafCohomology.OpenRestriction

section Transport

variable {C D : Type*} [Category C] [Category D]

/-- Transport a diagram through isomorphisms of its objects. -/
private def transportObjects (P : C ⥤ D) (Q : C → D) (e : ∀ U, P.obj U ≅ Q U) : C ⥤ D where
  obj := Q
  map {U V} i := (e U).inv ≫ P.map i ≫ (e V).hom
  map_id U :=
    (congrArg (fun g => (e U).inv ≫ g ≫ (e U).hom) (P.map_id U)).trans
      ((congrArg (fun g => (e U).inv ≫ g) (Category.id_comp (e U).hom)).trans
        (e U).inv_hom_id)
  map_comp i j := by
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- The transport leaves the diagram canonically isomorphic to the original. -/
private def transportObjectsIso (P : C ⥤ D) (Q : C → D) (e : ∀ U, P.obj U ≅ Q U) :
    P ≅ transportObjects P Q e :=
  NatIso.ofComponents e (fun {U V} i => by
    change P.map i ≫ (e V).hom = (e U).hom ≫ ((e U).inv ≫ P.map i ≫ (e V).hom)
    calc
      _ = (𝟙 (P.obj U)) ≫ (P.map i ≫ (e V).hom) := (Category.id_comp _).symm
      _ = ((e U).hom ≫ (e U).inv) ≫ (P.map i ≫ (e V).hom) :=
        congrArg (fun g => g ≫ (P.map i ≫ (e V).hom)) (e U).hom_inv_id.symm
      _ = _ := Category.assoc _ _ _)

end Transport

variable {X : TopCat.{0}} (F : AbelianSheaf X) (n : ℕ)

/-- The existing genuine cohomology of the restricted sheaf on an open subspace. -/
abbrev openCohomologyGroup (U : Opens X) : AddCommGrpCat.{0} :=
  AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((restriction U).obj F) n)

/-- The proved canonical open-subspace comparison, as an isomorphism
of the actual additive groups. -/
def openCohomologyIso (U : Opens X) :
    CategoryTheory.Sheaf.H'.{0} F n U ≅ openCohomologyGroup F n U :=
  (cohomologyEquiv U F n).toAddCommGrpIso

/-- The cohomology presheaf whose objects are literally `Hⁿ(U,F|U)`.
Its restriction maps are transported from the canonical Ext maps. -/
def openCohomologyPresheaf : TopCat.Presheaf AddCommGrpCat.{0} X :=
  transportObjects (CategoryTheory.Sheaf.cohomologyPresheaf F n)
    (fun U => openCohomologyGroup F n U.unop) (fun U => openCohomologyIso F n U.unop)

/-- This is naturally the actual Mathlib cohomology presheaf; only
the objects have been written as cohomology on the open subspaces. -/
def openCohomologyPresheafIso :
    CategoryTheory.Sheaf.cohomologyPresheaf F n ≅ openCohomologyPresheaf F n :=
  transportObjectsIso (CategoryTheory.Sheaf.cohomologyPresheaf F n)
    (fun U => openCohomologyGroup F n U.unop) (fun U => openCohomologyIso F n U.unop)

/-- The value is the genuine cohomology of the actual restriction. -/
theorem openCohomologyPresheaf_obj (U : Opens X) :
    (openCohomologyPresheaf F n).obj (op U) =
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((U.sheafRestrict).obj F) n) := rfl

variable {Y : TopCat.{0}} (f : X ⟶ Y) (y : Y)

/-- The directed system `U ↦ Hⁿ(f⁻¹(U),F|f⁻¹(U))` over actual open
neighborhoods of `y`, with the genuine cohomological restriction maps. -/
abbrev neighborhoodCohomologyDiagram : (OpenNhds y)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (OpenNhds.inclusion y).op ⋙ (Opens.map f).op ⋙ openCohomologyPresheaf F n

/-- Each term of the directed system is literal sheaf cohomology on
the actual inverse-image open subspace. -/
theorem neighborhoodCohomologyDiagram_obj (U : OpenNhds y) :
    (neighborhoodCohomologyDiagram F n f y).obj (op U) =
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        ((((Opens.map f).obj U.val).sheafRestrict).obj F) n) := rfl

/-- The directed system agrees canonically with the neighborhood
restriction of Mathlib's actual cohomology presheaf. -/
def neighborhoodCohomologyDiagramIso :
    (OpenNhds.inclusion y).op ⋙ (Opens.map f).op ⋙
        CategoryTheory.Sheaf.cohomologyPresheaf F n ≅
      neighborhoodCohomologyDiagram F n f y :=
  Functor.isoWhiskerLeft (OpenNhds.inclusion y).op
    (Functor.isoWhiskerLeft (Opens.map f).op (openCohomologyPresheafIso F n))

end Wikipedia.HopfProblem.SheafHigherDirectImage
