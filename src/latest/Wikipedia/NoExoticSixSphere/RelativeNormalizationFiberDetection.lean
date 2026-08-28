import Wikipedia.NoExoticSixSphere.EndingPathPairThreeRecovery
import Wikipedia.NoExoticSixSphere.RelativeNormalizationRecovery

/-!
# Third fiber homology detected by the actual fourth relative homology

Evaluation from the ending-path pair and its exact fiber section give
an explicit right inverse to the original normalized map. Naturality of
the descended map transports the checked auxiliary-pair recovery. No
naturality or recovery of a substitute prism is assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.RelativeNormalization

open RelativeFiberHomology EndingPathPair

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

namespace Data

variable {U a} (D : Data U a 1) [hF : SimplyConnectedSpace (Fiber U a)]
  [h₂ : Subsingleton (π_ 2 (Fiber U a) (HomotopyFiber.basepoint (subtypeInclusion U) a))]

include hF h₂ in
theorem fiberHomologyMap_recoveryLift_three (z : SingularHomology (Fiber U a) 3) :
    D.fiberHomologyMap (recoveryLift U a 1 z) = z :=
  D.fiberHomologyMap_recoveryLift (threeNormalizationData U a) z

include hF h₂ in
theorem fiberHomologyMap_surjective_three : Function.Surjective D.fiberHomologyMap :=
  fun z ↦ ⟨recoveryLift U a 1 z, D.fiberHomologyMap_recoveryLift_three z⟩

end Data

end NoExoticSixSphere.RelativeNormalization
