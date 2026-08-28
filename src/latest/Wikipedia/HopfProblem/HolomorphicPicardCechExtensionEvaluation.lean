import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionEvaluationBasic
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic

/-!
# Evaluation of actual sheafified extension sections

The universal property of genuine sheafification extends each literal
presheaf coordinate to a morphism into the actual intersection sheaf.
On presheaf-unit sections it is the original coordinate, and on the
included original sheaf it is exactly the original restriction map.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- The actual coordinate morphism from the genuine extension sheaf. -/
def evaluation (i : ι) : extensionSheaf c ⟶ intersectionSheaf F (U i) where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (evaluationPre c i) (intersectionSheaf F (U i)).property

/-- The actual sheafification unit followed by evaluation is the
original presheaf coordinate map. -/
theorem unit_evaluation (i : ι) :
    unit c ≫ (evaluation c i).hom = evaluationPre c i :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X)
    (evaluationPre c i) (intersectionSheaf F (U i)).property

@[simp] theorem evaluation_app_unit (i : ι) (V : Opens X) (s : ExtensionSection c V) :
    (evaluation c i).hom.app (op V) ((unit c).app (op V) s) =
      coordinateHom c V i s :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_evaluation c i) (op V)) s

/-- Evaluation is natural for actual restrictions, with literal
intersection sections on the target. -/
theorem evaluation_restrict (i : ι) {V T : Opens X} (hTV : T ≤ V)
    (s : Section (extensionSheaf c) V) :
    res F (inf_le_inf_right (U i) hTV) ((evaluation c i).hom.app (op V) s) =
      (evaluation c i).hom.app (op T) (res (extensionSheaf c) hTV s) :=
  res_map (evaluation c i) hTV s

/-- Inclusion followed by evaluation is the genuine restriction
morphism from the original sheaf. -/
theorem inclusion_evaluation (i : ι) :
    inclusion c ≫ evaluation c i = intersectionRestriction F (U i) := by
  apply CategoryTheory.Sheaf.hom_ext
  change (inclusionPre c ≫ unit c) ≫ (evaluation c i).hom =
    (intersectionRestriction F (U i)).hom
  rw [Category.assoc, unit_evaluation, inclusionPre_evaluationPre]

@[simp] theorem evaluation_app_inclusion (i : ι) (V : Opens X) (s : Section F V) :
    (evaluation c i).hom.app (op V) ((inclusion c).hom.app (op V) s) =
      res F inf_le_left s := by
  rw [inclusion_app, evaluation_app_unit, includeHom_coordinate]

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
