import Wikipedia.HopfProblem.SheafHigherDirectImageSheafificationBasic
import Wikipedia.HopfProblem.SheafHigherDirectImageCohomology
import Wikipedia.HopfProblem.SheafHigherDirectImageNeighborhoods

/-!
# Higher direct images as sheafifications of genuine cohomology presheaves

This is a proved description of the native right-derived pushforward,
not its definition.  Exact abelian sheafification converts the actual
injective-resolution computation into a sheaf isomorphism.  In the
second formulation the presheaf values are literal `Sheaf.H` groups on
the inverse-image open subspaces.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X) (n : ℕ)

/-- The genuine derived-pushforward sheaf is canonically the native
sheafification of the actual inverse-image cohomology presheaf. -/
def cohomologySheafificationIso :
    sheaf f F n ≅ (sheafification Y).obj
      ((Opens.map f).op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf F n) :=
  resolutionIso f F (injectiveResolution F) n ≪≫
    sheafHomologyIsoSheafification (pushedResolution f (injectiveResolution F)) n ≪≫
      (sheafification Y).mapIso
        (pushedResolutionCohomologyPresheafIso f (injectiveResolution F) n)

/-- Equivalently, sheafify the presheaf of literal cohomology groups
`Hⁿ(f⁻¹(U),F|f⁻¹(U))`, with the proved canonical restriction maps. -/
def openCohomologySheafificationIso :
    sheaf f F n ≅ (sheafification Y).obj
      ((Opens.map f).op ⋙ openCohomologyPresheaf F n) :=
  cohomologySheafificationIso f F n ≪≫
    (sheafification Y).mapIso
      (Functor.isoWhiskerLeft (Opens.map f).op (openCohomologyPresheafIso F n))

end Wikipedia.HopfProblem.SheafHigherDirectImage
