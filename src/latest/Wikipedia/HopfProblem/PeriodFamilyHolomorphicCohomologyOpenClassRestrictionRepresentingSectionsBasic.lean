import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreInteger
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionGlobal

/-!
# Literal sections of the original open-restriction representing map

The original degree-one section of the integer sheaf is sent to the restriction
of the original universal section. The formulas use the actual native sheaf
maps and the actual ambient image open, without replacing either sheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.RepresentingSections

open HolomorphicSheafCohomology
open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension

variable {X : TopCat.{0}} (A : Opens X)

/-- Restricting a genuine global section on the open subspace agrees with
restriction of its original ambient section along the literal image inclusion. -/
theorem restrictionGlobalEquiv_restrict (F : AbelianSheaf X) (V : Opens A)
    (s : ((OpenRestriction.restriction A).obj F).obj.obj (op (⊤ : Opens A))) :
    ((OpenRestriction.restriction A).obj F).obj.map
        (homOfLE (show V ≤ ⊤ from le_top)).op s =
      F.obj.map (homOfLE (OpenRestriction.openImage_obj_le A V)).op
        (OpenRestriction.restrictionGlobalEquiv A F s) := by
  let r : V ⟶ (⊤ : Opens A) := homOfLE le_top
  let e : op ((OpenRestriction.openImage A).obj ⊤) ⟶ op A :=
    eqToHom (congrArg op (OpenRestriction.openImage_top A))
  let i : (OpenRestriction.openImage A).obj V ⟶ A :=
    homOfLE (OpenRestriction.openImage_obj_le A V)
  change F.obj.map ((OpenRestriction.openImage A).map r).op s =
    F.obj.map i.op (F.obj.map e s)
  have he : e ≫ i.op = ((OpenRestriction.openImage A).map r).op := Subsingleton.elim _ _
  have hm : F.obj.map e ≫ F.obj.map i.op =
      F.obj.map ((OpenRestriction.openImage A).map r).op :=
    (F.obj.map_comp e i.op).symm.trans (congrArg F.obj.map he)
  exact (ConcreteCategory.congr_hom hm s).symm

/-- On every original open of the subspace, the original representing-section
comparison sends degree one to the restriction of its genuine universal section. -/
theorem homRestrictionEquiv_degreeUnit_app (F : AbelianSheaf X)
    (g : OpenRestriction.freeOpen A ⟶ F) (V : Opens A) :
    (OpenRestriction.homRestrictionEquiv A F g).hom.app (op V)
        ((degreeUnit (TopCat.of A)).app (op V) (ULift.up (1 : ℤ))) =
      F.obj.map (homOfLE (OpenRestriction.openImage_obj_le A V)).op
        (OpenRestriction.freeHomEquiv A F g) := by
  let η := OpenRestriction.homRestrictionEquiv A F g
  let r : V ⟶ (⊤ : Opens A) := homOfLE le_top
  let s := η.hom.app (op (⊤ : Opens A))
    ((degreeUnit (TopCat.of A)).app (op (⊤ : Opens A)) (ULift.up (1 : ℤ)))
  have hU := ConcreteCategory.congr_hom
    ((degreeUnit (TopCat.of A)).naturality r.op) (ULift.up (1 : ℤ))
  change (degreeUnit (TopCat.of A)).app (op V) (ULift.up (1 : ℤ)) =
    (integerSheaf (TopCat.of A)).obj.map r.op
      ((degreeUnit (TopCat.of A)).app (op (⊤ : Opens A)) (ULift.up (1 : ℤ))) at hU
  have hη := ConcreteCategory.congr_hom (η.hom.naturality r.op)
    ((degreeUnit (TopCat.of A)).app (op (⊤ : Opens A)) (ULift.up (1 : ℤ)))
  have hs : OpenRestriction.restrictionGlobalEquiv A F s =
      OpenRestriction.freeHomEquiv A F g :=
    (congrArg (OpenRestriction.restrictionGlobalEquiv A F)
      (CechFibre.homGlobalEquiv_degreeUnit (TopCat.of A)
        ((OpenRestriction.restriction A).obj F) η).symm).trans
          (OpenRestriction.homRestrictionEquiv_sections A F g)
  exact (congrArg (fun z => η.hom.app (op V) z) hU).trans
    (hη.trans ((restrictionGlobalEquiv_restrict A F V s).trans
      (congrArg (fun z => F.obj.map
        (homOfLE (OpenRestriction.openImage_obj_le A V)).op z) hs)))

end OpenClassRestriction.RepresentingSections
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
