import Wikipedia.NoExoticSixSphere.EndingPathPair
import Wikipedia.NoExoticSixSphere.RelativeSingularHomologyMaps

/-! # The original ending-path evaluation lift in every degree -/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeNormalization

open RelativeFiberHomology EndingPathPair

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def recoveryLift (n : ℕ) :
    SingularHomology (Fiber U a) (n + 2) →ₗ[ℤ] RelativeSingularHomology.Homology U (n + 3) :=
  (RelativeSingularHomology.map (evaluation U a) (evaluation_mapsTo U a) (n + 3)).comp
    ((transgression (subspace U a) (basepoint U a) (n + 2)).comp
      (singularHomologyMap (liftSection U a) (n + 2)))

end NoExoticSixSphere.RelativeNormalization
