import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepSixTorsion
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSingular

/-!
# Vanishing of actual second integral singular cohomology

The original delta-circle sweep proves that six annihilates every actual
second homology class. Hence every integral functional on that group is
zero. The preceding first homology group was already proved zero and
free, so the degree-local universal-coefficient evaluation isomorphism
proves second cohomology zero. No torsion-freeness or vanishing of second
homology is presumed, and no Poincare-duality comparison is used.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondCohomology

open SingularMayerVietoris SingularCohomologyFree

/-- Every actual integral functional on second homology is zero. -/
theorem homologyTwo_dual_eq_zero (φ : SingularHomology Space 2 →ₗ[ℤ] ℤ) : φ = 0 := by
  apply LinearMap.ext
  intro a
  have h := congrArg φ (DeltaSweep.six_zsmul_homologyTwo a)
  rw [map_zsmul, map_zero] at h
  change (6 : ℤ) * φ a = 0 at h
  change φ a = 0
  omega

theorem homologyTwo_dual_subsingleton :
    Subsingleton (SingularHomology Space 2 →ₗ[ℤ] ℤ) :=
  ⟨fun a b => (homologyTwo_dual_eq_zero a).trans (homologyTwo_dual_eq_zero b).symm⟩

/-- The actual second-cohomology evaluation equivalence uses only
the proved first-degree freeness. -/
def evaluationTwoEquiv :
    SingularCohomology Space 2 ≃ₗ[ℤ] (SingularHomology Space 2 →ₗ[ℤ] ℤ) := by
  letI := LowDegrees.singularH1_free
  exact LocalEvaluation.singularEvaluationSuccEquiv Space 1

@[simp] theorem evaluationTwoEquiv_apply (a : SingularCohomology Space 2) :
    evaluationTwoEquiv a = singularEvaluation Space 2 a := rfl

/-- The original integral singular second cohomology group is zero. -/
theorem cohomologyTwo_subsingleton : Subsingleton (SingularCohomology Space 2) := by
  have := homologyTwo_dual_subsingleton
  exact evaluationTwoEquiv.injective.subsingleton

theorem cohomologyTwo_eq_zero (a : SingularCohomology Space 2) : a = 0 := by
  have := cohomologyTwo_subsingleton
  exact Subsingleton.elim _ _

theorem cohomologyTwo_isZero : IsZero (SingularCohomology Space 2) := by
  have := cohomologyTwo_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem cohomologyTwo_finrank : Module.finrank ℤ (SingularCohomology Space 2) = 0 := by
  have := cohomologyTwo_subsingleton
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondCohomology
