import Wikipedia.NoExoticSixSphere.EndingPathPairRecovery
import Wikipedia.NoExoticSixSphere.ContractibleNativeHomotopy
import Wikipedia.NoExoticSixSphere.HomotopyFiberProjectionThree
import Wikipedia.NoExoticSixSphere.RelativeThreeNormalizationData
import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberNaturality
import Wikipedia.HopfProblem.OrbitPairHigherHomotopyHomeomorph

/-!
# Recovery in third homology for the actual ending-path pair

Native target homotopy vanishes at every initial point. The source is
homeomorphic to the original fiber, so its second homotopy vanishes when
the original fiber is two-connected. The actual fiber sequence supplies
the remaining connectivity inputs and the third Hurewicz isomorphism
proves projection bijectivity. The two connecting identities give recovery.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.EndingPathPair

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

variable [h₂ : Subsingleton
  (π_ 2 (Fiber U a) (HomotopyFiber.basepoint (subtypeInclusion U) a))]

include h₂ in
theorem subspace_piTwo_subsingleton : Subsingleton (π_ 2 (subspace U a) (basepoint U a)) := by
  let e := HigherHomotopyCoordinates.homeomorphEquiv (Fin 2) (homeomorph U a)
    (HomotopyFiber.basepoint (subtypeInclusion U) a)
  exact e.symm.injective.subsingleton

include h₂ in
theorem fiber_piTwo_subsingleton : Subsingleton
    (π_ 2 (Fiber (subspace U a) (basepoint U a))
      (HomotopyFiber.basepoint (subtypeInclusion (subspace U a)) (basepoint U a))) := by
  let := subspace_piTwo_subsingleton U a
  let : Subsingleton (π_ 2 (subspace U a)
      ((HomotopyFiber.projection (subtypeInclusion (subspace U a))
        ((subtypeInclusion (subspace U a)) (basepoint U a)))
        (HomotopyFiber.basepoint (subtypeInclusion (subspace U a)) (basepoint U a)))) :=
    subspace_piTwo_subsingleton U a
  let : Subsingleton (π_ 2 (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    ContractibleNativeHomotopy.subsingleton 2 _
  let : Subsingleton (π_ 3 (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    ContractibleNativeHomotopy.subsingleton 3 _
  exact (HomotopyFiberConnectivity.projection_pi_bijective 2
    (subtypeInclusion (subspace U a)) (basepoint U a)).injective.subsingleton

variable [hF : SimplyConnectedSpace (Fiber U a)]

def threeNormalizationData : RelativeNormalization.Data (subspace U a) (basepoint U a) 1 := by
  let := subspace_simplyConnected U a
  let : SimplyConnectedSpace (Fiber (subspace U a) (basepoint U a)) := fiber_simplyConnected U a
  let : Subsingleton (π_ 2 (Fiber (subspace U a) (basepoint U a))
      (HomotopyFiber.basepoint (subtypeInclusion (subspace U a)) (basepoint U a))) :=
    fiber_piTwo_subsingleton U a
  exact RelativeThreeSkeletonNormalization.data (subspace U a) (basepoint U a)
    (inclusion_surjective_at U a 3) (inclusion_surjective_at U a 2 (basepoint U a))

include hF h₂ in
theorem projection_homologyThree_bijective :
    Function.Bijective (singularHomologyMap
      (HomotopyFiber.projection (subtypeInclusion (subspace U a)) (basepoint U a).val) 3) := by
  let := subspace_simplyConnected U a
  let := subspace_piTwo_subsingleton U a
  let : Subsingleton (π_ 2 (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    ContractibleNativeHomotopy.subsingleton 2 _
  let : Subsingleton (π_ 3 (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    ContractibleNativeHomotopy.subsingleton 3 _
  let : Subsingleton (π_ 4 (EndingPath.Space a.val)
      ((subtypeInclusion (subspace U a)) (basepoint U a))) :=
    ContractibleNativeHomotopy.subsingleton 4 _
  exact HomotopyFiberConnectivity.projection_homologyThree_bijective
    (subtypeInclusion (subspace U a)) (basepoint U a)

theorem homologyMap_transgression_three
    (z : SingularHomology (Fiber (subspace U a) (basepoint U a)) 3) :
    (threeNormalizationData U a).fiberHomologyMap
      (transgression (subspace U a) (basepoint U a) 3 z) = z := by
  apply (projection_homologyThree_bijective U a).injective
  have h := LinearMap.congr_fun (threeNormalizationData U a).projection_fiberHomologyMap
    (transgression (subspace U a) (basepoint U a) 3 z)
  have ht := connecting_transgression (subspace U a) (basepoint U a) 3 z
  rw [CuspCentralHomology.singularHomologyMap_const_eq_zero _ _ 3 (by decide),
    LinearMap.zero_apply, sub_zero] at ht
  exact h.trans ht

end NoExoticSixSphere.EndingPathPair
