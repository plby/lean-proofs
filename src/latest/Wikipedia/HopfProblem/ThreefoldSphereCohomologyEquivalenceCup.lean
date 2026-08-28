import Wikipedia.HopfProblem.ThreefoldSphereCohomologyEquivalenceBasic
import Wikipedia.HopfProblem.SingularCohomologyCupClasses

/-!
# Cup compatibility of the actual sphere cohomology equivalence

The integral pullback equivalences preserve the original Alexander--Whitney
cup operations in all degrees. Their inverses preserve the same operations
in the other direction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereCohomologyEquivalence

open SingularCohomologyFree SingularCohomologyCup

/-- The actual sphere-map pullback preserves the native cup product in every pair of degrees. -/
theorem cohomologyEquiv_cupProduct (x : Space) (p q : ℕ)
    (a : SingularCohomology Space p) (b : SingularCohomology Space q) :
    cohomologyEquiv x (p + q) (cupProduct Space p q a b) =
      cupProduct SixSphere p q (cohomologyEquiv x p a) (cohomologyEquiv x q b) := by
  simpa only [cohomologyEquiv_apply] using
    cupProduct_pullback (SphereHomologyEquivalence.sphereMap x) p q a b

/-- The inverse equivalences preserve the original cup products as well. -/
theorem cohomologyEquiv_symm_cupProduct (x : Space) (p q : ℕ)
    (a : SingularCohomology SixSphere p) (b : SingularCohomology SixSphere q) :
    (cohomologyEquiv x (p + q)).symm (cupProduct SixSphere p q a b) =
      cupProduct Space p q ((cohomologyEquiv x p).symm a)
        ((cohomologyEquiv x q).symm b) := by
  apply (cohomologyEquiv x (p + q)).injective
  simp only [LinearEquiv.apply_symm_apply, cohomologyEquiv_cupProduct]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereCohomologyEquivalence
