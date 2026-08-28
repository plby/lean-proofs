import Wikipedia.HopfProblem.SheafHigherDirectImageHomology
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Local computation of actual higher direct images

An injective resolution gives a genuine complex of pushed-forward
sheaves.  Exactness of stalks identifies the stalk of its cohomology
sheaf with the directed colimit of its presheaf cohomology.  Evaluation
on an open set is explicitly evaluation of the original resolution on
the inverse-image open set.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F : AbelianSheaf X}

/-- Apply actual sheaf pushforward degreewise to an injective resolution. -/
abbrev pushedResolution (I : InjectiveResolution F) :
    CochainComplex (AbelianSheaf Y) ℕ :=
  ((pushforward f).mapHomologicalComplex _).obj I.cocomplex

/-- Cohomology of the actual underlying complex of pushed-forward presheaves. -/
abbrev resolutionPresheaf (I : InjectiveResolution F) (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat Y := homologyPresheaf (pushedResolution f I) n

/-- The genuine stalk of the derived pushforward is the stalk of the
presheaf cohomology of any pushed-forward injective resolution. -/
def resolutionStalkIso (I : InjectiveResolution F) (n : ℕ) (y : Y) :
    TopCat.Presheaf.stalk (sheaf f F n).obj y ≅
      TopCat.Presheaf.stalk (resolutionPresheaf f I n) y :=
  (TopCat.Sheaf.forget AddCommGrpCat Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat y).mapIso
      (resolutionIso f F I n) ≪≫
    stalkHomologyPresheafIso y (pushedResolution f I) n

/-- The actual directed neighborhood diagram of resolution cohomology. -/
abbrev resolutionNeighborhoodDiagram (I : InjectiveResolution F) (n : ℕ) (y : Y) :
    (OpenNhds y)ᵒᵖ ⥤ AddCommGrpCat :=
  (OpenNhds.inclusion y).op ⋙ resolutionPresheaf f I n

/-- The stalk comparison is a colimit over all actual open neighborhoods,
ordered by shrinking; no properness or fibre hypotheses are used. -/
def resolutionStalkColimitIso (I : InjectiveResolution F) (n : ℕ) (y : Y) :
    TopCat.Presheaf.stalk (sheaf f F n).obj y ≅
      colimit (resolutionNeighborhoodDiagram f I n y) :=
  resolutionStalkIso f I n y

/-- The source resolution evaluated on the actual inverse-image open set. -/
abbrev inverseImageSectionComplex (I : InjectiveResolution F) (U : Opens Y) :
    CochainComplex AddCommGrpCat ℕ := by
  let E : AbelianSheaf X ⥤ AddCommGrpCat.{0} := TopCat.Sheaf.forget AddCommGrpCat X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ((Opens.map f).obj U))
  let _ : E.Additive := ⟨by intros; rfl⟩
  exact (E.mapHomologicalComplex _).obj I.cocomplex

/-- At every open set, the resolution cohomology presheaf is the actual
cohomology of sections of the resolution on the inverse image. -/
def resolutionPresheafObjIso (I : InjectiveResolution F) (n : ℕ) (U : Opens Y) :
    (resolutionPresheaf f I n).obj (op U) ≅
      (inverseImageSectionComplex f I U).homology n := by
  let E : TopCat.Presheaf AddCommGrpCat.{0} Y ⥤ AddCommGrpCat.{0} :=
    (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op U)
  let _ : E.Additive := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits E := inferInstanceAs
    (PreservesFiniteLimits ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))
  let _ : PreservesFiniteColimits E := inferInstanceAs
    (PreservesFiniteColimits ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))
  exact (mapComplexHomologyIso (underlyingPresheafComplex (pushedResolution f I)) E n).symm

end Wikipedia.HopfProblem.SheafHigherDirectImage
