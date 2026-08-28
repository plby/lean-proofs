import Wikipedia.HopfProblem.ThreefoldHomologyMiddleVanishing
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSingular

/-!
# Vanishing of the actual middle integral singular cohomology

The genuine second, third, and fourth integral homology groups vanish.
The original degree-local universal-coefficient evaluation maps are
therefore isomorphisms in degrees three and four, and their integral
duals are zero.  This proves the original third and fourth cohomology
groups vanish without a duality or sphere-recognition hypothesis.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.MiddleCohomology

open SingularMayerVietoris SingularCohomologyFree

/-- The actual third-cohomology evaluation, using the proved second-homology vanishing. -/
def evaluationThreeEquiv :
    SingularCohomology Space 3 ≃ₗ[ℤ] (SingularHomology Space 3 →ₗ[ℤ] ℤ) := by
  letI := SecondDegree.homologyTwo_subsingleton
  exact LocalEvaluation.singularEvaluationSuccEquiv Space 2

@[simp] theorem evaluationThreeEquiv_apply (a : SingularCohomology Space 3) :
    evaluationThreeEquiv a = singularEvaluation Space 3 a := rfl

/-- The actual fourth-cohomology evaluation, using the proved third-homology vanishing. -/
def evaluationFourEquiv :
    SingularCohomology Space 4 ≃ₗ[ℤ] (SingularHomology Space 4 →ₗ[ℤ] ℤ) := by
  letI := ThirdDegree.homologyThree_subsingleton
  exact LocalEvaluation.singularEvaluationSuccEquiv Space 3

@[simp] theorem evaluationFourEquiv_apply (a : SingularCohomology Space 4) :
    evaluationFourEquiv a = singularEvaluation Space 4 a := rfl

/-- The original third integral singular cohomology group is zero. -/
theorem cohomologyThree_subsingleton : Subsingleton (SingularCohomology Space 3) := by
  have := ThirdDegree.homologyThree_subsingleton
  exact evaluationThreeEquiv.injective.subsingleton

theorem cohomologyThree_eq_zero (a : SingularCohomology Space 3) : a = 0 :=
  cohomologyThree_subsingleton.elim _ _

theorem cohomologyThree_isZero : IsZero (SingularCohomology Space 3) := by
  have := cohomologyThree_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem cohomologyThree_finrank : Module.finrank ℤ (SingularCohomology Space 3) = 0 := by
  have := cohomologyThree_subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- The original fourth integral singular cohomology group is zero. -/
theorem cohomologyFour_subsingleton : Subsingleton (SingularCohomology Space 4) := by
  have := FourthDegree.homologyFour_subsingleton
  exact evaluationFourEquiv.injective.subsingleton

theorem cohomologyFour_eq_zero (a : SingularCohomology Space 4) : a = 0 :=
  cohomologyFour_subsingleton.elim _ _

theorem cohomologyFour_isZero : IsZero (SingularCohomology Space 4) := by
  have := cohomologyFour_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem cohomologyFour_finrank : Module.finrank ℤ (SingularCohomology Space 4) = 0 := by
  have := cohomologyFour_subsingleton
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.MiddleCohomology
