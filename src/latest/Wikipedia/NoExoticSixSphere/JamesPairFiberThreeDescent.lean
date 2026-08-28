import Wikipedia.NoExoticSixSphere.JamesPairFourCycles
import Wikipedia.NoExoticSixSphere.RelativeThreeNormalizationData
import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberNaturality

/-!
# The actual relative-fourth to fiber-third map for the original James pair

The original coherent normalization satisfies every field of the generic
construction. Its actual fiber classes therefore descend through the
original relative fourth homology. Projection is the original connecting
map. The later detection module proves surjectivity and third fiber
homology vanishing by a separate ending-path recovery argument.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization

open ComparisonCylinder

attribute [local instance] PairNormalization.cylinderSimplyConnected
attribute [local instance] PairNormalization.sourceSimplyConnected
attribute [local instance] fiberSimplyConnected fiberPiTwo

def normalizationData (n : ℕ) (a : sourceImage (n + 2)) :
    RelativeNormalization.Data (sourceImage (n + 2)) a 1 :=
  RelativeThreeSkeletonNormalization.data (sourceImage (n + 2)) a
    (PairNormalization.inclusion_piThree_surjective n)
    (PairNormalization.inclusion_piTwo_surjective n a)

theorem normalizationData_homotopy (n d : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex d, Cylinder (n + 2))) :
    (normalizationData n a).homotopy d smp = homotopy n d a smp := rfl

def fiberHomologyMap (n : ℕ) (a : sourceImage (n + 2)) :
    RelativeSingularHomology.Homology (sourceImage (n + 2)) 4 →ₗ[ℤ]
      SingularHomology (SourceFiber (n + 2) a) 3 :=
  (normalizationData n a).fiberHomologyMap

theorem fiberHomologyMap_simplex (n : ℕ) (a : sourceImage (n + 2))
    (smp : RelativeSimplexCycles.RelativeSimplex (sourceImage (n + 2)) 4)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin 5)) = a.val) :
    fiberHomologyMap n a (RelativeSimplexCycles.homologyClass (sourceImage (n + 2)) 3 smp) =
      RelativeSimplexFiberClass.fiberClass (sourceImage (n + 2)) a 1 smp hv :=
  (normalizationData n a).fiberHomologyMap_simplex_eq_fiberClass smp hv

theorem projection_fiberHomologyMap (n : ℕ) (a : sourceImage (n + 2)) :
    (singularHomologyMap (HomotopyFiber.projection (subtypeInclusion (sourceImage (n + 2)))
      a.val) 3).comp (fiberHomologyMap n a) =
        RelativeSingularHomology.connecting (sourceImage (n + 2)) 3 :=
  (normalizationData n a).projection_fiberHomologyMap

theorem fiberHomologyMap_apply_eq_zero (n : ℕ) (a : sourceImage (n + 2))
    (z : RelativeSingularHomology.Homology (sourceImage (n + 2)) 4) :
    fiberHomologyMap n a z = 0 := by
  rw [relative_homology_eq_zero (n + 2) 4 (by omega) z, map_zero]

end NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization
