import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClass
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassOperationsCocycles

/-!
# Bundle-isomorphism invariance and product-factor additivity of the native Chern class

The first Chern class here is the class constructed from genuine native
edge-section boundary winding. Its proved comparison with the negative
factor-log cocycle transfers the actual logarithmic branch-coboundary
identities to singular cohomology.

The product statement concerns the constructed pointwise product factor.
It does not assert an identification with an actual tensor-product bundle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationUniqueness
open PeriodTorusLineBundleChernLog ChernCocycle ChernCover SingularCohomologyFree

variable {p : PeriodDomain}

/-- The actual bundle-isomorphism branch gives an explicit incoming singular coboundary. -/
theorem firstChernCochain_bundleIso {F G : FactorOfAutomorphy p} (e : BundleIso F G) :
    firstChernCochain G = firstChernCochain F +
      ((singularCochainComplex p.Torus).d 1 2).hom
        (oneCochain (edgeCocycle p) (fun x => bundleIsoLogBranch e (p.latticeEquiv.symm x))) := by
  rw [firstChernCochain_eq_twoCochain G, firstChernCochain_eq_twoCochain F,
    factorCoordinateCocycle_bundleIso e]
  simp only [twoCochain_neg, twoCochain_add, twoCochain_coboundary]
  abel

/-- The actual product branch is the positive coboundary correction between obstruction cochains. -/
theorem firstChernCochain_factorProduct (F G : FactorOfAutomorphy p) :
    firstChernCochain (factorProduct F G) = firstChernCochain F + firstChernCochain G +
      ((singularCochainComplex p.Torus).d 1 2).hom
        (oneCochain (edgeCocycle p)
          (fun x => factorProductLogBranch F G (p.latticeEquiv.symm x))) := by
  rw [firstChernCochain_eq_twoCochain (factorProduct F G),
    firstChernCochain_eq_twoCochain F, firstChernCochain_eq_twoCochain G,
    factorCoordinateCocycle_product]
  simp only [twoCochain_neg, twoCochain_add, twoCochain_coboundary]
  abel

/-- An actual analytic isomorphism of the native bundles preserves their first Chern classes. -/
theorem firstChernClass_bundleIso {F G : FactorOfAutomorphy p} (e : BundleIso F G) :
    firstChernClass F = firstChernClass G := by
  rw [firstChernClass_eq_neg_twoClass F, firstChernClass_eq_neg_twoClass G]
  exact congrArg Neg.neg (factorCoordinateTwoClass_bundleIso e)

/-- The actual pointwise product factor has the sum of the native first Chern classes. -/
theorem firstChernClass_factorProduct (F G : FactorOfAutomorphy p) :
    firstChernClass (factorProduct F G) = firstChernClass F + firstChernClass G := by
  rw [firstChernClass_eq_neg_twoClass (factorProduct F G),
    firstChernClass_eq_neg_twoClass F, firstChernClass_eq_neg_twoClass G,
    factorCoordinateTwoClass_product]
  exact (neg_add_rev _ _).trans (add_comm _ _)

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
