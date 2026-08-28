import Wikipedia.NoExoticSixSphere.RelativeThreeSkeletonNormalization
import Wikipedia.NoExoticSixSphere.RelativeNormalizationData

/-! # The checked three-skeleton family as actual normalization data -/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.RelativeThreeSkeletonNormalization

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  [SimplyConnectedSpace (Fiber U a)]
  [Subsingleton (π_ 2 (Fiber U a) (HomotopyFiber.basepoint (subtypeInclusion U) a))]
  (hπ₃ : ∀ b : U, Function.Surjective
    (HigherHomotopy.map (N := Fin 3) (subtypeInclusion U) (y := b) rfl))
  (hπ₂ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

def data : RelativeNormalization.Data U a 1 where
  homotopy := homotopy U a hπ₃ hπ₂
  initial := homotopy_zero U a hπ₃ hπ₂
  face := homotopy_face U a hπ₃ hπ₂
  preserves := homotopy_mem U a hπ₃ hπ₂
  vertices := endpoint_verticesBased U a hπ₃ hπ₂
  edge := endpoint_edge U a hπ₃ hπ₂
  lower_mem := endpoint_tetrahedron_mem U a hπ₃ hπ₂
  constant_zero := homotopy_const_zero U a hπ₃ hπ₂

end NoExoticSixSphere.RelativeThreeSkeletonNormalization
