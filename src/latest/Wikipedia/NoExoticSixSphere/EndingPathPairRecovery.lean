import Wikipedia.NoExoticSixSphere.EndingPathHigherHomotopy
import Wikipedia.NoExoticSixSphere.HomotopyFiberProjectionTwo
import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberProjection
import Wikipedia.NoExoticSixSphere.RelativeFiberConnecting
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull

/-!
# Recovery for the actual ending-path pair

Projection is bijective on second homology because the ambient ending-path
space has trivial second and third homotopy. Comparing the two actual
connecting-map formulas then recovers every second homology class of the
new inclusion fiber from its original evaluation prism.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.EndingPathPair

open RelativeFiberHomology RelativeNormalizedFiberClasses

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  [SimplyConnectedSpace (Fiber U a)]

theorem projection_homologyTwo_bijective :
    Function.Bijective (singularHomologyMap
      (HomotopyFiber.projection (subtypeInclusion (subspace U a)) (basepoint U a).val) 2) := by
  let := subspace_simplyConnected U a
  let : Subsingleton (π_ 2 (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    EndingPath.homotopy_subsingleton a.val 2
  let : Subsingleton (π_ 3 (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    EndingPath.homotopy_subsingleton a.val 3
  exact HomotopyFiberConnectivity.projection_homologyTwo_bijective
    (subtypeInclusion (subspace U a)) (basepoint U a)

theorem homologyMap_transgression
    (z : SingularHomology (Fiber (subspace U a) (basepoint U a)) 2) :
    let _ := subspace_simplyConnected U a
    homologyMap (subspace U a) (basepoint U a) (inclusion_surjective U a 2)
      (transgression (subspace U a) (basepoint U a) 2 z) = z := by
  let := subspace_simplyConnected U a
  apply (projection_homologyTwo_bijective U a).injective
  have h := LinearMap.congr_fun
    (projection_homologyMap (subspace U a) (basepoint U a) (inclusion_surjective U a 2))
    (transgression (subspace U a) (basepoint U a) 2 z)
  have ht := connecting_transgression (subspace U a) (basepoint U a) 2 z
  rw [
    CuspCentralHomology.singularHomologyMap_const_eq_zero _ _ 2 (by decide),
    LinearMap.zero_apply, sub_zero] at ht
  exact h.trans ht

end NoExoticSixSphere.EndingPathPair
