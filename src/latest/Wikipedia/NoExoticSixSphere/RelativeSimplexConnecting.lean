import Wikipedia.NoExoticSixSphere.RelativeBoundaryFiberComparison
import Wikipedia.NoExoticSixSphere.RelativeFiberConnecting

/-!
# The actual connecting map of a relative simplex

Its lifted boundary is the original signed boundary cycle mapped into
the source. Projecting the whole-boundary fiber lift gives this exact
source map, so projection of the raw fiber class equals the original
pair connecting class, with its actual sign.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.RelativeSimplexConnecting

open RelativeSingularHomology RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

def boundaryCycle (n : ℕ) (smp : RelativeSimplex U (n + 2)) :
    ModuleHomology.Cycle (singularComplex U) (n + 1) :=
  ModuleHomology.mapCycles (singularChainMap (RelativeBoundaryFiberClass.source U (n + 2) smp))
    (n + 1) (SimplexBoundaryChains.cycle n)

theorem boundaryCycle_val (n : ℕ) (smp : RelativeSimplex U (n + 2)) :
    (boundaryCycle U n smp).val =
      inducedChain (RelativeBoundaryFiberClass.source U (n + 2) smp) (n + 1)
        (SimplexBoundaryChains.chain (n + 1)) :=
  ModuleHomology.mapCycles_val _ _ _

theorem included_boundaryCycle (n : ℕ) (smp : RelativeSimplex U (n + 2)) :
    inducedChain (subtypeInclusion U) (n + 1) (boundaryCycle U n smp).val =
      ((singularComplex X).d (n + 2) (n + 1)).hom (simplexChain X (n + 2) smp.val) := by
  rw [boundaryCycle_val]
  change ((inducedChain (subtypeInclusion U) (n + 1)).comp
    (inducedChain (RelativeBoundaryFiberClass.source U (n + 2) smp) (n + 1))) _ = _
  rw [← inducedChain_comp]
  have he : (subtypeInclusion U).comp (RelativeBoundaryFiberClass.source U (n + 2) smp) =
      smp.val.comp (subtypeInclusion (simplexBoundary (n + 2))) := rfl
  rw [he, inducedChain_comp, LinearMap.comp_apply, SimplexBoundaryChains.inclusion_chain,
    inducedChain_boundary, inducedChain_simplex, ContinuousMap.comp_id]

theorem connecting_homologyClass (n : ℕ) (smp : RelativeSimplex U (n + 2)) :
    connecting U (n + 1) (homologyClass U (n + 1) smp) =
      ModuleHomology.cycleClass (singularComplex U) (n + 1) (boundaryCycle U n smp) :=
  connectingMap_cycleClass (sequence_shortExact U) (n + 1)
    (cycle U (n + 1) smp) (simplexChain X (n + 2) smp.val) rfl
    (boundaryCycle U n smp) (included_boundaryCycle U n smp)

theorem connecting_source_homologyMap (n : ℕ) (smp : RelativeSimplex U (n + 2)) :
    connecting U (n + 1) (homologyClass U (n + 1) smp) =
      singularHomologyMap (RelativeBoundaryFiberClass.source U (n + 2) smp) (n + 1)
        (ModuleHomology.cycleClass (singularComplex (SimplexBoundary (n + 2))) (n + 1)
          (SimplexBoundaryChains.cycle n)) := by
  rw [connecting_homologyClass]
  exact (ModuleHomology.homologyMap_cycleClass _ _ _).symm

theorem projection_boundaryClass (a : U) (n : ℕ) (smp : RelativeSimplex U (n + 2))
    (v : Simplex (n + 2)) (hv : smp.val v = a.val) :
    singularHomologyMap (HomotopyFiber.projection (subtypeInclusion U) a.val) (n + 1)
        (RelativeBoundaryFiberClass.homologyClass U a n smp v hv) =
      connecting U (n + 1) (homologyClass U (n + 1) smp) := by
  unfold RelativeBoundaryFiberClass.homologyClass
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  have he : (HomotopyFiber.projection (subtypeInclusion U) a.val).comp
      (RelativeBoundaryFiberClass.lift U a (n + 2) smp v hv) =
        RelativeBoundaryFiberClass.source U (n + 2) smp := rfl
  rw [he, ← connecting_source_homologyMap]

theorem projection_fiberClass (a : U) (n : ℕ) (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    singularHomologyMap (HomotopyFiber.projection (subtypeInclusion U) a.val) (n + 2)
        (RelativeSimplexFiberClass.fiberClass U a n smp hv) =
      connecting U (n + 2) (homologyClass U (n + 2) smp) := by
  rw [← RelativeBoundaryFiberClass.homologyClass_firstVertex U a n smp hv]
  exact projection_boundaryClass U a (n + 1) smp (stdSimplex.vertex 0) hv

end NoExoticSixSphere.RelativeSimplexConnecting
