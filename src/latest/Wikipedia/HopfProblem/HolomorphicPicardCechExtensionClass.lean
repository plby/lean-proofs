import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# The genuine degree-one cohomology class of a Čech cocycle

The class is the existing derived-category `Ext¹` class of the proved
short exact extension. Its source is literally the native constant
sheaf on `ULift ℤ`, so the result is actual `CategoryTheory.Sheaf.H F 1`,
not a replacement cochain group or an assumed comparison class.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- The actual sheaf-cohomology class of the constructed genuine
short exact extension, with no extension-existence assumption. -/
def classOf (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    CategoryTheory.Sheaf.H.{0} F 1 :=
  (complex_shortExact c hU).extClass

theorem classOf_eq_extClass (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    classOf c hU = (complex_shortExact c hU).extClass := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
