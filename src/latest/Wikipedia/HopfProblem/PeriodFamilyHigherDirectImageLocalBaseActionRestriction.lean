import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionCoefficient

/-!
# Original neighborhood restriction is linear over local base restriction

For arbitrary nested base opens, native degree-one cohomology restriction
commutes with a holomorphic multiplier defined only on the larger open.
The actions are the original coefficient-induced open-base actions, and
the comparison is the original nested holomorphic open comparison.
No global extension, stalk action, local generation, or base change is
assumed in this compatibility theorem.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology
open PeriodFamilyHolomorphicCohomology.OpenClassRestriction

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The original ambient-open cohomology-presheaf map on actual full preimages. -/
abbrev neighborhoodRestriction (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (q : ℕ) :
    OpenClasses.neighborhoodCohomology P W q ⟶ OpenClasses.neighborhoodCohomology P U q :=
  (CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) q).map
    (homOfLE (Zero.basePreimage_mono P h)).op

/-- The canonical holomorphic open comparison respects the original
degree-one cohomology-presheaf restriction between full preimages. -/
theorem openCohomologyEquiv_restrict (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (x : OpenClasses.neighborhoodCohomology P W 1) :
    preimageHolomorphicPullback P h 1 (OpenClasses.openCohomologyEquiv P W 1 x) =
      OpenClasses.openCohomologyEquiv P U 1 (neighborhoodRestriction P h 1 x) := by
  let := P.totalChartedSpace
  exact HolomorphicCohomology.pullback_nested IT (Zero.basePreimage_mono P h) x

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Arbitrary native neighborhood restriction is semilinear for the
literal restriction of a base function defined only on the larger open. -/
theorem neighborhoodRestriction_smul (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (g : Zero.BaseSection P W)
    (x : OpenClasses.neighborhoodCohomology P W 1) :
    letI := OpenBaseAction.neighborhoodCohomologyModule P W 1
    letI := OpenBaseAction.neighborhoodCohomologyModule P U 1
    neighborhoodRestriction P h 1 (g • x) =
      Zero.baseRestriction P h g • neighborhoodRestriction P h 1 x := by
  let := OpenBaseAction.neighborhoodCohomologyModule P W 1
  let := OpenBaseAction.neighborhoodCohomologyModule P U 1
  apply (OpenClasses.openCohomologyEquiv P U 1).injective
  have hw := OpenBaseAction.openCohomologyEquiv_smul_map P W 1 g x
  have hp := preimageHolomorphicPullback_baseMultiply P h 1 g
    (OpenClasses.openCohomologyEquiv P W 1 x)
  have hn := openCohomologyEquiv_restrict P h x
  have hu := OpenBaseAction.openCohomologyEquiv_smul_map P U 1
    (Zero.baseRestriction P h g) (neighborhoodRestriction P h 1 x)
  exact (openCohomologyEquiv_restrict P h (g • x)).symm.trans
    ((congrArg (preimageHolomorphicPullback P h 1) hw).trans
      (hp.trans ((congrArg
        (CategoryTheory.Sheaf.H.map
          (OpenBaseAction.preimageMultiplyEnd P U (Zero.baseRestriction P h g)) 1)
        hn).trans hu.symm)))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
