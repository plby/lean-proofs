import Wikipedia.NoExoticSixSphere.EndingPathPair
import Wikipedia.NoExoticSixSphere.EndingPathLoopContraction
import Wikipedia.NoExoticSixSphere.HomotopyFiberNullhomotopyCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual ending-path fiber projection is a homology isomorphism in every degree

The specified nullhomotopy identifies the new fiber with its source times
the actual loop space of the ending-path space. Those loops contract by
pointwise shortening. The inverse equivalence preserves the source
coordinate exactly, identifying its composite with the original projection.
No connectivity or Hurewicz assumption is needed.
-/

noncomputable section

open scoped ContinuousMap
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.EndingPathPair

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def fiberProductEquiv :
    Fiber (subspace U a) (basepoint U a) ≃ₕ (subspace U a × EndingPath.Loops a.val) :=
  HomotopyFiberHomotopyInvariance.nullhomotopyEquiv
    (subtypeInclusion (subspace U a)) (basepoint U a).val
    ((EndingPath.contraction (y₀ := a.val)).compContinuousMap (subtypeInclusion (subspace U a)))

theorem projection_fiberProductEquiv_symm :
    (HomotopyFiber.projection (subtypeInclusion (subspace U a)) (basepoint U a).val).comp
      (fiberProductEquiv U a).invFun = ContinuousMap.fst := by
  apply ContinuousMap.ext
  intro p
  exact HomotopyFiberHomotopyInvariance.nullhomotopyEquiv_symm_source
    (subtypeInclusion (subspace U a)) (basepoint U a).val
    ((EndingPath.contraction (y₀ := a.val)).compContinuousMap (subtypeInclusion (subspace U a)))
    p.1 p.2

theorem projection_homology_bijective (n : ℕ) :
    Function.Bijective (singularHomologyMap
      (HomotopyFiber.projection (subtypeInclusion (subspace U a)) (basepoint U a).val) n) := by
  let : ContractibleSpace (EndingPath.Loops a.val) := EndingPath.loops_contractible a.val
  let E := fiberProductEquiv U a
  let P : (subspace U a × EndingPath.Loops a.val) ≃ₕ subspace U a :=
    (Homeomorph.prodComm _ _).toHomotopyEquiv.trans
      (CircleTopology.contractibleProdHomotopyEquiv (EndingPath.Loops a.val) (subspace U a))
  have hp : Function.Bijective
      (singularHomologyMap (ContinuousMap.fst : C(subspace U a × EndingPath.Loops a.val,
        subspace U a)) n) := (homotopyEquivHomologyEquiv P n).bijective
  have he : Function.Bijective (singularHomologyMap E.invFun n) :=
    (homotopyEquivHomologyEquiv E.symm n).bijective
  let p := HomotopyFiber.projection (subtypeInclusion (subspace U a)) (basepoint U a).val
  have hc := singularHomologyMap_comp E.invFun p n
  rw [projection_fiberProductEquiv_symm U a] at hc
  have hcomp : singularHomologyMap p n ∘ singularHomologyMap E.invFun n =
      singularHomologyMap (ContinuousMap.fst : C(subspace U a × EndingPath.Loops a.val,
        subspace U a)) n := funext (fun z ↦ (LinearMap.congr_fun hc z).symm)
  apply (Function.Bijective.of_comp_iff (singularHomologyMap p n) he).mp
  rw [hcomp]
  exact hp

end NoExoticSixSphere.EndingPathPair
