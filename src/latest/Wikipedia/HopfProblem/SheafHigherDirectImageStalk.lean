import Wikipedia.HopfProblem.SheafHigherDirectImageCohomology
import Wikipedia.HopfProblem.SheafHigherDirectImageNeighborhoods

/-!
# The general stalk formula for genuine higher direct images

For every continuous map `f`, abelian sheaf `F`, point `y`, and degree `n`,
the actual stalk of `Rⁿf_*F` is the directed colimit of
`Hⁿ(f⁻¹(U),F|f⁻¹(U))` over all open neighborhoods `U` of `y`.

Here `Rⁿf_*` is the native right-derived sheaf pushforward, and every
cohomology group is Mathlib's existing Ext-defined `Sheaf.H`.  The proof
uses actual injective resolutions, exactness of stalks, and the proved
open-subspace comparison.  There are no properness, fibre, or base-change
assumptions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X) (n : ℕ) (y : Y)

/-- The actual derived-pushforward stalk is the stalk of the actual
source cohomology presheaf evaluated on inverse-image opens. -/
def stalkCohomologyPresheafIso :
    TopCat.Presheaf.stalk (sheaf f F n).obj y ≅
      TopCat.Presheaf.stalk
        ((Opens.map f).op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf F n) y :=
  resolutionStalkIso f (injectiveResolution F) n y ≪≫
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).mapIso
      (pushedResolutionCohomologyPresheafIso f (injectiveResolution F) n)

/-- The general stalk formula: the directed colimit contains literal
`Sheaf.H` groups on the actual inverse-image open subspaces. -/
def stalkNeighborhoodCohomologyIso :
    TopCat.Presheaf.stalk (sheaf f F n).obj y ≅
      colimit (neighborhoodCohomologyDiagram F n f y) :=
  stalkCohomologyPresheafIso f F n y ≪≫
    colim.mapIso (neighborhoodCohomologyDiagramIso F n f y)

/-- Additive-equivalence form of the general higher-direct-image stalk formula. -/
def stalkNeighborhoodCohomologyEquiv :
    ↥(TopCat.Presheaf.stalk (sheaf f F n).obj y) ≃+
      ↥(colimit (neighborhoodCohomologyDiagram F n f y)) :=
  (stalkNeighborhoodCohomologyIso f F n y).addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.SheafHigherDirectImage
