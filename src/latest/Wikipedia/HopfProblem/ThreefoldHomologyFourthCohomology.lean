import Wikipedia.HopfProblem.ThreefoldHomologyBoundaryFreeness
import Wikipedia.HopfProblem.ThreefoldHomologyFourthAttachment
import Wikipedia.HopfProblem.ThreefoldHomologyFifthDegree
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSingular

/-!
# Fourth homology is free and fifth integral cohomology vanishes

The actual degree-four attachment map is surjective, so the original
singular connecting map embeds fourth homology in the actual degree-three
overlap product. The latter is now proved free using the genuine cap and
Wang maps. Finite generation makes fourth homology free. Degree-local
universal coefficients and the already proved fifth-homology vanishing
then prove that actual fifth integral singular cohomology is zero.

No Poincare duality, sphere recognition, or value of the still-uncomputed
fourth homology rank is used or asserted.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthCohomology

open SingularMayerVietoris SingularCohomologyFree

/-- The genuine fourth integral homology has no torsion, via its original connecting map. -/
theorem homologyFour_torsionFree : Module.IsTorsionFree ℤ (SingularHomology Space 4) := by
  have := BoundaryFreeness.starOverlapHomology_positive_torsionFree 2
  exact Function.Injective.moduleIsTorsionFree
    (starConnectingHomomorphism 3) FourthDegree.connecting_three_injective
    (fun r a => (starConnectingHomomorphism 3).map_smul r a)

/-- Fourth homology is a genuine finite free integral module; its rank is not assumed. -/
theorem homologyFour_free : Module.Free ℤ (SingularHomology Space 4) := by
  have := homologyFour_torsionFree
  have := Finiteness.homology_finite 4
  infer_instance

/-- The actual fifth-cohomology evaluation map is an isomorphism, using only adjacent freeness. -/
def evaluationFiveEquiv :
    SingularCohomology Space 5 ≃ₗ[ℤ] (SingularHomology Space 5 →ₗ[ℤ] ℤ) := by
  letI := homologyFour_free
  exact LocalEvaluation.singularEvaluationSuccEquiv Space 4

@[simp] theorem evaluationFiveEquiv_apply (a : SingularCohomology Space 5) :
    evaluationFiveEquiv a = singularEvaluation Space 5 a := rfl

/-- The original fifth integral singular cohomology group vanishes. -/
theorem cohomologyFive_subsingleton : Subsingleton (SingularCohomology Space 5) := by
  have := FifthDegree.homologyFive_subsingleton
  exact evaluationFiveEquiv.injective.subsingleton

theorem cohomologyFive_eq_zero (a : SingularCohomology Space 5) : a = 0 := by
  have := cohomologyFive_subsingleton
  exact Subsingleton.elim _ _

theorem cohomologyFive_isZero : IsZero (SingularCohomology Space 5) := by
  have := cohomologyFive_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem cohomologyFive_finrank : Module.finrank ℤ (SingularCohomology Space 5) = 0 := by
  have := cohomologyFive_subsingleton
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthCohomology
