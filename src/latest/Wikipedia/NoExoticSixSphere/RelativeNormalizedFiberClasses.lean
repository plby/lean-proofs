import Wikipedia.NoExoticSixSphere.RelativeNormalizedThreeHomology
import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberHomotopy

/-!
# A genuine fiber-homology assignment on normalized tetrahedra

The checked two-skeleton normalization has based vertices and subspace
boundary in degree three. The actual cone construction therefore assigns
a fiber second-homology class to each original singular tetrahedron.
The linear assignment kills subspace chains. Vanishing on four-boundaries
and recovery of transgression are still separate, unproved obligations.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeNormalizedFiberClasses

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

def simplexClass (smp : C(Simplex 3, X)) : SingularHomology (Fiber U a) 2 :=
  RelativeSimplexFiberClass.fiberClass U a 0
    (RelativeNormalizedThreeHomology.relativeSimplex U a hπ smp)
    (RelativeTwoSkeletonNormalization.endpoint_verticesBased U a hπ 3 smp 0)

def classOperator : Chains X 3 →ₗ[ℤ] SingularHomology (Fiber U a) 2 :=
  chainLift X 3 (simplexClass U a hπ)

theorem classOperator_simplex (smp : C(Simplex 3, X)) :
    classOperator U a hπ (simplexChain X 3 smp) = simplexClass U a hπ smp :=
  chainLift_simplex X 3 _ smp

theorem simplexClass_eq_zero_of_mem (smp : C(Simplex 3, X)) (hs : ∀ s, smp s ∈ U) :
    simplexClass U a hπ smp = 0 :=
  RelativeSimplexFiberClass.fiberClass_eq_zero_of_mem U a 0 _ _
    (RelativeTwoSkeletonNormalization.endpoint_mem U a hπ 3 smp hs)

theorem classOperator_supported (c : Chains X 3) (hc : c ∈ supportedChainSubmodule U 3) :
    classOperator U a hπ c = 0 := by
  have hle : supportedChainSubmodule U 3 ≤ LinearMap.ker (classOperator U a hπ) := by
    rw [supportedChainSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨smp, hs, rfl⟩
    change classOperator U a hπ (simplexChain X 3 smp) = 0
    rw [classOperator_simplex]
    exact simplexClass_eq_zero_of_mem U a hπ smp (fun s ↦ hs ⟨s, rfl⟩)
  exact hle hc

end NoExoticSixSphere.RelativeNormalizedFiberClasses
