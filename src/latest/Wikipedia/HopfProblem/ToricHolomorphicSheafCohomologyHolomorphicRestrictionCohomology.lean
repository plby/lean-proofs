import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionSheaf
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestriction

/-!
# Actual holomorphic cohomology of an ambient open and its submanifold

The genuine all-degree open-restriction Ext comparison is composed with
the constructed literal holomorphic sheaf isomorphism. Thus Mathlib's
actual cohomology-presheaf group of the ambient holomorphic sheaf on `U`
is identified with its actual holomorphic sheaf cohomology as an open
submanifold, in every degree.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- Genuine ambient-open cohomology is genuine holomorphic cohomology
of the actual open submanifold, with no sheaf-identification premise. -/
def cohomologyEquiv (U : Opens M) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) n U ≃+
      CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I U) n :=
  (OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
    (HolomorphicFunctionSheaf.additiveSheaf I M) n).trans
      (((CategoryTheory.Sheaf.functorH _ n).mapIso (sheafIso I U)).addCommGroupIsoToAddEquiv)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction
