import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupAcyclicOverlap
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestriction

/-!
# Actual ambient-open cohomology of the incidence blowup overlap

The actual holomorphic restriction isomorphism and the literal overlap
biholomorphism identify the genuine cohomology-presheaf group used by
Mayer--Vietoris with genuine holomorphic cohomology of `ℂ × ℂ*`.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupAcyclic

open AffineBlowup ToricCharts

/-- The actual ambient-open `H'` group is actual holomorphic cohomology
of the punctured product, not a replacement cochain group. -/
def overlapOpenCohomologyEquiv (b : Bool) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) Space) n overlapOpen ≃+
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) puncturedOpen) n :=
  (HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) overlapOpen n).trans
    (overlapCohomologyEquiv b n)

/-- The corresponding actual restricted sheaf has the same genuine
cohomology via the constructed holomorphic sheaf isomorphism. -/
def overlapRestrictionCohomologyEquiv (b : Bool) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0}
      ((OpenRestriction.restriction (X := TopCat.of Space) overlapOpen).obj
        (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) Space)) n ≃+
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) puncturedOpen) n := by
  let e := (CategoryTheory.Sheaf.functorH _ n).mapIso
    (HolomorphicRestriction.sheafIso 𝓘(ℂ, CoordinateSpace 2) overlapOpen)
  exact e.addCommGroupIsoToAddEquiv.trans (overlapCohomologyEquiv b n)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupAcyclic
