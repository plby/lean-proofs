import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberDescent
import Wikipedia.NoExoticSixSphere.RelativeNormalizationPairHomotopy

/-!
# The descended map on an original relative simplex

When the first vertex is already based, the actual normalization is a
pair homotopy fixing that vertex. The checked pair-homotopy invariance
therefore identifies the normalized fiber class with the raw cone-path
class. This removes normalization from the simplex representative formula.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeNormalizedFiberClasses

open RelativeSimplexCycles RelativeTwoSkeletonNormalization

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

theorem simplexClass_eq_fiberClass (smp : RelativeSimplex U 3)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val) :
    simplexClass U a hπ smp.val = RelativeSimplexFiberClass.fiberClass U a 0 smp hv :=
  RelativeSimplexFiberClass.fiberClass_eq_of_pairHomotopy U a 0 smp
    (RelativeNormalizedThreeHomology.relativeSimplex U a hπ smp.val) hv
    (endpoint_verticesBased U a hπ 3 smp.val 0) (pairHomotopy U a hπ 3 smp.val)
    (homotopy_boundary U a hπ 2 smp.val smp.property)
    (homotopy_vertex U a hπ 3 smp.val 0 hv)

theorem homologyMap_simplex_eq_fiberClass (smp : RelativeSimplex U 3)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val) :
    homologyMap U a hπ (homologyClass U 2 smp) =
      RelativeSimplexFiberClass.fiberClass U a 0 smp hv := by
  rw [homologyMap_simplex, simplexClass_eq_fiberClass U a hπ smp hv]

theorem homologyMap_simplex_eq_boundaryClass (smp : RelativeSimplex U 3)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val) :
    homologyMap U a hπ (homologyClass U 2 smp) =
      RelativeBoundaryFiberClass.homologyClass U a 1 smp (stdSimplex.vertex 0) hv := by
  rw [homologyMap_simplex_eq_fiberClass U a hπ smp hv,
    RelativeBoundaryFiberClass.homologyClass_firstVertex U a 0 smp hv]

end NoExoticSixSphere.RelativeNormalizedFiberClasses
