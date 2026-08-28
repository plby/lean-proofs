import Wikipedia.HopfProblem.HolomorphicPicardCechRefinementExtension
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass
import Wikipedia.HopfProblem.HolomorphicPicardExtEquivalence

/-!
# Refinement preserves the actual degree-one sheaf-cohomology class

The equality follows from the constructed morphism of genuine short
exact extensions, fixing their two original endpoints. It is not a
comparison with a separately defined Čech quotient by assumption.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι κ : Type} {U : ι → Opens X} {V : κ → Opens X}
    (r : κ → ι) (hr : ∀ a, V a ≤ U (r a)) (c : CechOneCocycle F U)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ a, x ∈ V a)

theorem classOf_refinement :
    classOf (Cech.refinement F r hr c) hV = classOf c hU := by
  exact (ExtExtensions.extClass_eq_of_middle_map
    (complex_shortExact c hU) (complex_shortExact (Cech.refinement F r hr c) hV)
    (refinementMap r hr c) (inclusion_refinementMap r hr c)
    (refinementMap_projection r hr c)).symm

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
