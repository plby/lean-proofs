import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleClass
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCover
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogFactorOperations

/-!
# Actual product and bundle-isomorphism operations on factor cocycle classes

The actual logarithmic branch corrections are transported to the original
integer period coordinates. They are genuine group coboundaries and hence
do not change the constructed native singular class. The resulting laws
concern the actual pointwise product factor and actual analytic bundle
isomorphisms. No identification of that product with a tensor bundle is
asserted here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationUniqueness
open PeriodTorusLineBundleChernLog ChernCocycle ChernCover

variable {p : PeriodDomain}

/-- The actual product branch correction in the original integral period coordinates. -/
theorem factorCoordinateCocycle_product (F G : FactorOfAutomorphy p) :
    factorCoordinateCocycle (factorProduct F G) =
      (factorCoordinateCocycle F + factorCoordinateCocycle G) +
        -IntegralTwoCocycle.coboundary
          (fun x => factorProductLogBranch F G (p.latticeEquiv.symm x)) := by
  apply IntegralTwoCocycle.ext
  intro x y
  simp only [factorCoordinateCocycle_apply, factorCocycle_product,
    IntegralTwoCocycle.add_apply, IntegralTwoCocycle.neg_apply,
    IntegralTwoCocycle.coboundary_apply, map_add]

/-- An actual analytic bundle isomorphism gives this coordinate branch coboundary. -/
theorem factorCoordinateCocycle_bundleIso {F G : FactorOfAutomorphy p}
    (e : BundleIso F G) :
    factorCoordinateCocycle G = factorCoordinateCocycle F +
      -IntegralTwoCocycle.coboundary
        (fun x => bundleIsoLogBranch e (p.latticeEquiv.symm x)) := by
  apply IntegralTwoCocycle.ext
  intro x y
  simp only [factorCoordinateCocycle_apply, factorCocycle_bundleIso e,
    IntegralTwoCocycle.add_apply, IntegralTwoCocycle.neg_apply,
    IntegralTwoCocycle.coboundary_apply, map_add]

/-- The genuine native singular class of the product cocycle is the sum of the classes. -/
theorem factorCoordinateTwoClass_product (F G : FactorOfAutomorphy p) :
    twoClass (edgeCocycle p) (factorCoordinateCocycle (factorProduct F G)) =
      twoClass (edgeCocycle p) (factorCoordinateCocycle F) +
        twoClass (edgeCocycle p) (factorCoordinateCocycle G) := by
  rw [factorCoordinateCocycle_product]
  simp only [twoClass_add, twoClass_neg, twoClass_coboundary, neg_zero, add_zero]

/-- Actual analytic bundle isomorphisms preserve the genuine native factor cocycle class. -/
theorem factorCoordinateTwoClass_bundleIso {F G : FactorOfAutomorphy p}
    (e : BundleIso F G) :
    twoClass (edgeCocycle p) (factorCoordinateCocycle F) =
      twoClass (edgeCocycle p) (factorCoordinateCocycle G) := by
  rw [factorCoordinateCocycle_bundleIso e]
  simp only [twoClass_add, twoClass_neg, twoClass_coboundary, neg_zero, add_zero]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
