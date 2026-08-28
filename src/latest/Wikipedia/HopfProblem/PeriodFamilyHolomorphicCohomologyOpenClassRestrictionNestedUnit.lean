import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedGeometry
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionRepresentingSections
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingUnit
import Wikipedia.HopfProblem.SheafHigherDirectImageSectionsBasic

/-!
# The actual representing endpoint for nested-open restriction

The free-open map for an original inclusion and the two original open
representing units fit the canonical nested restriction comparison.
Equality is checked on their genuine global degree-one sections, where
both sides restrict the same original free-open universal section.
No naturality of higher cohomology is assumed in this endpoint proof.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyFinitePushforward SheafHigherDirectImage.Sections

variable {X : TopCat.{0}} {U W : Opens X}

/-- The original integer and free-open endpoints commute under the
actual nested restriction isomorphism and the native free-open map. -/
theorem nested_representingUnit (h : U ≤ W) :
    Embedding.integerUnit (nestedInclusion h) (nestedEmbedding h) ≫
        (Embedding.restriction (nestedInclusion h) (nestedEmbedding h)).map
          (OpenRestriction.representingUnit W) ≫
        (nestedRestrictionIso h).hom.app (OpenRestriction.freeOpen W) =
      OpenRestriction.representingUnit U ≫
        (OpenRestriction.restriction U).map
          ((freeOpenFunctor X).map (homOfLE h)) := by
  let F := OpenRestriction.freeOpen W
  let φ : OpenRestriction.freeOpen U ⟶ F := (freeOpenFunctor X).map (homOfLE h)
  let s := OpenRestriction.freeHomEquiv W F (𝟙 F)
  let V : Opens W := nestedImageOpen h ⊤
  let iW : (OpenRestriction.openImage W).obj V ⟶ W :=
    homOfLE (OpenRestriction.openImage_obj_le W V)
  let iU : (OpenRestriction.openImage U).obj ⊤ ⟶ U :=
    homOfLE (OpenRestriction.openImage_obj_le U ⊤)
  let r : U ⟶ W := homOfLE h
  let e := (eqToHom (nestedImageOpen_ambient h (⊤ : Opens U)).symm).op
  apply (homGlobalEquiv (TopCat.of U) ((OpenRestriction.restriction U).obj F)).injective
  change (((nestedRestrictionIso h).hom.app F).hom.app (op (⊤ : Opens U)))
      ((OpenRestriction.representingUnit W).hom.app (op V)
        ((Embedding.integerUnit (nestedInclusion h) (nestedEmbedding h)).hom.app
          (op (⊤ : Opens U))
          ((degreeUnit (TopCat.of U)).app (op (⊤ : Opens U)) (ULift.up (1 : ℤ))))) =
    φ.hom.app (op ((OpenRestriction.openImage U).obj ⊤))
      ((OpenRestriction.representingUnit U).hom.app (op (⊤ : Opens U))
        ((degreeUnit (TopCat.of U)).app (op (⊤ : Opens U)) (ULift.up (1 : ℤ))))
  have hleft := (congrArg
    (((nestedRestrictionIso h).hom.app F).hom.app (op (⊤ : Opens U)))
    ((congrArg ((OpenRestriction.representingUnit W).hom.app (op V))
      (Embedding.integerUnit_degreeUnit_app (nestedInclusion h) (nestedEmbedding h)
        ⊤ (ULift.up (1 : ℤ)))).trans
      (RepresentingSections.representingUnit_degreeUnit_app W V))).trans
      (ConcreteCategory.congr_hom (nestedRestrictionIso_hom_app h F ⊤) _)
  have hφ : OpenRestriction.freeHomEquiv U F φ = F.obj.map r.op s :=
    (congrArg (OpenRestriction.freeHomEquiv U F) (Category.comp_id φ)).symm.trans
      (freeHomEquiv_naturality_open r F (𝟙 F))
  have hright := (RepresentingSections.representingUnit_comp_degreeUnit_app U F φ ⊤).trans
    (congrArg (F.obj.map iU.op) hφ)
  have he : iW.op ≫ e = r.op ≫ iU.op := Subsingleton.elim _ _
  have hm : F.obj.map iW.op ≫ F.obj.map e = F.obj.map r.op ≫ F.obj.map iU.op :=
    (F.obj.map_comp iW.op e).symm.trans
      ((congrArg F.obj.map he).trans (F.obj.map_comp r.op iU.op))
  exact hleft.trans ((ConcreteCategory.congr_hom hm s).trans hright.symm)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
