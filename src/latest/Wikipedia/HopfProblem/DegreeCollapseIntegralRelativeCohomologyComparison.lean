import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenSupportCohomology
import Wikipedia.NoExoticSixSphere.RelativeHomologyMapComparison

/-!
# Original integral cohomology comparison from actual relative homology

Actual relative integral chain modules are free. A quasi-isomorphism of
these bounded-below complexes is a chain homotopy equivalence, whose
original dual computes the original cochain pullback. No homology
vanishing or projectivity of homology groups is required.
-/

noncomputable section

open CategoryTheory HomologicalComplex Function

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open SingularCohomologyFree NoExoticSixSphere

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)

theorem cohomologyPullback_bijective_of_homology
    (h : ∀ n, Bijective (RelativeSingularHomology.map f hf n)) (p : ℕ) :
    Bijective (cohomologyPullback f hf p) := by
  let K := RelativeSingularHomology.complex U
  let L := RelativeSingularHomology.complex V
  let (n : ℕ) : Projective (K.X n) := by
    let : Module.Free ℤ (K.X n) := RelativeSingularHomology.chains_free U n
    infer_instance
  let (n : ℕ) : Projective (L.X n) := by
    let : Module.Free ℤ (L.X n) := RelativeSingularHomology.chains_free V n
    infer_instance
  let : QuasiIso (RelativeSingularHomology.mapChain f hf) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (h n)
  let := IntegralCochainTransport.dualMap_quasiIso_of_projective
    (RelativeSingularHomology.mapChain f hf)
  let e := isoOfQuasiIsoAt (dualMap (RelativeSingularHomology.mapChain f hf)) p
  exact e.toLinearEquiv.bijective

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
