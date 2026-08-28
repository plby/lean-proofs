import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberRawSimplex
import Wikipedia.NoExoticSixSphere.RelativeSimplexConnecting

/-!
# Projection of the descended fiber map is the original connecting map

The raw relative-simplex identity has the correct connecting sign.
The actual normalized relative simplex classes generate relative third
homology, so that identity determines the equality on the whole original
homology object.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.RelativeNormalizedFiberClasses

open RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

theorem projection_homologyMap :
    (singularHomologyMap (HomotopyFiber.projection (subtypeInclusion U) a.val) 2).comp
        (homologyMap U a hπ) = connecting U 2 := by
  have he : ((singularHomologyMap (HomotopyFiber.projection (subtypeInclusion U) a.val) 2).comp
        (homologyMap U a hπ)).comp (RelativeNormalizedThreeHomology.classOperator U a hπ) =
      (connecting U 2).comp (RelativeNormalizedThreeHomology.classOperator U a hπ) := by
    apply chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, RelativeNormalizedThreeHomology.classOperator_simplex]
    rw [homologyMap_simplex_eq_fiberClass U a hπ
      (RelativeNormalizedThreeHomology.relativeSimplex U a hπ smp)
      (RelativeTwoSkeletonNormalization.endpoint_verticesBased U a hπ 3 smp 0)]
    rw [RelativeNormalizedThreeHomology.classOperator_simplex]
    exact RelativeSimplexConnecting.projection_fiberClass U a 0
      (RelativeNormalizedThreeHomology.relativeSimplex U a hπ smp)
      (RelativeTwoSkeletonNormalization.endpoint_verticesBased U a hπ 3 smp 0)
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := RelativeNormalizedThreeHomology.classOperator_surjective U a hπ z
  exact LinearMap.congr_fun he c

end NoExoticSixSphere.RelativeNormalizedFiberClasses
