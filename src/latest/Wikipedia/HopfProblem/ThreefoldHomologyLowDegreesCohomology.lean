import Wikipedia.HopfProblem.ThreefoldHomologyLowDegreesCohomologyPrimitive
import Wikipedia.HopfProblem.ThreefoldFundamentalGroup

/-!
# The constructed threefold has zero integral first cohomology

This is the native integral singular cohomology of the actual glued
space.  Its vanishing follows from the already proved simple connectedness
and the actual path-primitive construction, with no additional hypotheses.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LowDegrees

/-- Every actual integral degree-one singular cohomology class vanishes. -/
theorem singularH1Cohomology_eq_zero
    (a : SingularCohomologyFree.SingularCohomology Space 1) : a = 0 := by
  have := space_simplyConnected
  exact ThreefoldCohomologyPath.singularH1Cohomology_eq_zero_of_simplyConnected Space a

/-- The actual first integral singular cohomology is the zero module. -/
theorem singularH1Cohomology_subsingleton :
    Subsingleton (SingularCohomologyFree.SingularCohomology Space 1) :=
  ⟨fun a b => (singularH1Cohomology_eq_zero a).trans
    (singularH1Cohomology_eq_zero b).symm⟩

/-- Vanishing as a zero object in the category of integral modules. -/
theorem singularH1Cohomology_isZero :
    CategoryTheory.Limits.IsZero
      (SingularCohomologyFree.SingularCohomology Space 1) :=
  ModuleCat.isZero_iff_subsingleton.mpr singularH1Cohomology_subsingleton

/-- Explicit rank-zero coordinates for the actual integral cohomology. -/
noncomputable def singularH1CohomologyEquivZero :
    SingularCohomologyFree.SingularCohomology Space 1 ≃ₗ[ℤ] (Fin 0 → ℤ) := by
  have := singularH1Cohomology_subsingleton
  exact LinearEquiv.ofSubsingleton _ _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LowDegrees
