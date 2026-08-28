import Wikipedia.HopfProblem.HolomorphicPicardCechCoboundaryExtension
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass
import Wikipedia.HopfProblem.HolomorphicPicardExtEquivalence

/-!
# Actual local coboundaries preserve the genuine cohomology class

The proof uses the explicitly constructed change-of-splitting map of
genuine extensions and its identity maps on their original endpoints.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (c d : CechOneCocycle F U)
    (hU : ∀ x : X, ∃ i, x ∈ U i)

theorem classOf_eq_of_coboundary (b : Cech.ZeroCochain F U)
    (hb : c - d = Cech.coboundary F U b) : classOf c hU = classOf d hU := by
  exact ExtExtensions.extClass_eq_of_middle_map
    (complex_shortExact c hU) (complex_shortExact d hU) (coboundaryMap c d b hb)
    (inclusion_coboundaryMap c d b hb) (coboundaryMap_projection c d b hb)

theorem classOf_eq_of_solvable_sub (h : (c - d).Solvable) :
    classOf c hU = classOf d hU := by
  obtain ⟨b, hb⟩ := h
  apply classOf_eq_of_coboundary c d hU b
  exact (Cech.cocycle_ext F U hb).symm

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
