import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassInjectivityTwo
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassInjectivityGlobalKernel

/-!
# Exact period-character kernels in the original neighborhood cohomology

The genuine original neighborhood comparison preserves zero. Applying
the proved period-character kernel theorem to the actual restricted
family identifies the kernel of all four coefficient functions on
every original base open. This concerns the period-character map only,
not generation of the full neighborhood cohomology group.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The original neighborhood period class vanishes exactly when the
actual restricted-family global extension class vanishes. -/
theorem openClass_eq_zero_iff_restrictedClass (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.Coefficients (V := V) U) :
    OpenClasses.periodClass P U a = 0 ↔
      Cocycle.periodClass (Restriction.restrictedPeriods P U) a = 0 := by
  constructor
  · intro ha
    exact (OpenClasses.periodClass_comparison P U a).symm.trans
      ((congrArg (OpenClasses.neighborhoodCohomologyEquiv P U 1) ha).trans
        (map_zero (OpenClasses.neighborhoodCohomologyEquiv P U 1)))
  · intro ha
    apply (OpenClasses.neighborhoodCohomologyEquiv P U 1).injective
    exact (OpenClasses.periodClass_comparison P U a).trans
      (ha.trans (map_zero (OpenClasses.neighborhoodCohomologyEquiv P U 1)).symm)

/-- All four original holomorphic coefficient functions have zero native
neighborhood class exactly when their original period reduction vanishes pointwise. -/
theorem openClass_eq_zero_iff_reduction (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.Coefficients (V := V) U) :
    OpenClasses.periodClass P U a = 0 ↔
      ∀ b : U, MarkedLinear.reduction (P.point b) (fun j => a j b) = 0 :=
  (openClass_eq_zero_iff_restrictedClass P U a).trans
    (periodClass_eq_zero_iff_reduction (Restriction.restrictedPeriods P U) a)

/-- The kernel consists exactly of actual holomorphic linear period
characters, explicitly reconstructed from the last two original coefficients. -/
theorem openClass_eq_zero_iff_linearCoefficients (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.Coefficients (V := V) U) :
    OpenClasses.periodClass P U a = 0 ↔
      a = Cocycle.linearCoefficients (Restriction.restrictedPeriods P U) ![a 2, a 3] :=
  (openClass_eq_zero_iff_restrictedClass P U a).trans
    (periodClass_eq_zero_iff_linearCoefficients (Restriction.restrictedPeriods P U) a)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity
