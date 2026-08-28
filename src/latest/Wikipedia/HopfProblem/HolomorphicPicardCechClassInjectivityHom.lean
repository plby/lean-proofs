import Wikipedia.HopfProblem.HolomorphicPicardCechClassInjectivityCriterion
import Wikipedia.HopfProblem.HolomorphicPicardCechClassAdditive

/-!
# The genuine cover-cohomology homomorphism is injective

The map is the already constructed additive map into native sheaf `H¹`.
Actual quotient induction and the independently proved fixed-cover
equality criterion show that it is injective.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  {ι : Type} {U : ι → Opens X} (hU : ∀ x : X, ∃ i : ι, x ∈ U i)

/-- Actual fixed-cover Čech cohomology embeds by the constructed additive
class map into genuine degree-one sheaf cohomology. -/
theorem coverCohomologyClassHom_injective :
    Function.Injective (coverCohomologyClassHom F hU) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro c d h
  change Cech.classOf F U c = Cech.classOf F U d
  apply (CechClassInjectivity.classOf_eq_iff_coverClass_eq c d hU).mp
  change classOf c hU = classOf d hU at h
  exact h

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
