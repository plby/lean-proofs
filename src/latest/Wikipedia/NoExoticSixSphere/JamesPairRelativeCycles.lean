import Wikipedia.NoExoticSixSphere.JamesPairSimplexNormalization
import Wikipedia.NoExoticSixSphere.RelativeNormalizedThreeHomology

/-!
# Normalized relative three-cycle classes for the original James pair

Every connectivity input to the generic construction is discharged for
the actual mapping cylinder and its source image. The resulting map on
the original singular chains has the checked representative formula,
preserves relative classes, and kills both subspace chains and actual
four-boundaries. Transgression injectivity is not asserted.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.PairNormalization

open ComparisonCylinder RelativeSingularHomology

attribute [local instance] cylinderSimplyConnected sourceSimplyConnected

def relativeTetrahedron (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 3, Cylinder (n + 2))) :
    RelativeSimplexCycles.RelativeSimplex (sourceImage (n + 2)) 3 :=
  ⟨endpoint n 3 a smp, endpoint_tetrahedron_boundary n a smp⟩

def classOperator (n : ℕ) (a : sourceImage (n + 2)) :
    Chains (Cylinder (n + 2)) 3 →ₗ[ℤ] Homology (sourceImage (n + 2)) 3 :=
  RelativeNormalizedThreeHomology.classOperator (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a)

theorem classOperator_simplex (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 3, Cylinder (n + 2))) :
    classOperator n a (simplexChain (Cylinder (n + 2)) 3 smp) =
      RelativeSimplexCycles.homologyClass (sourceImage (n + 2)) 2
        (relativeTetrahedron n a smp) :=
  RelativeNormalizedThreeHomology.classOperator_simplex _ _ _ smp

theorem classOperator_eq (n : ℕ) (a : sourceImage (n + 2))
    (c : Chains (Cylinder (n + 2)) 3)
    (hc : ((complex (sourceImage (n + 2))).d 3 2).hom
      (quotientMap (sourceImage (n + 2)) 3 c) = 0) :
    classOperator n a c = ModuleHomology.cycleClass (complex (sourceImage (n + 2))) 3
      (ModuleHomology.mkCycle (complex (sourceImage (n + 2))) 3
        (quotientMap (sourceImage (n + 2)) 3 c) hc) :=
  RelativeNormalizedThreeHomology.classOperator_eq _ _ _ c hc

theorem classOperator_supported (n : ℕ) (a : sourceImage (n + 2))
    (c : Chains (Cylinder (n + 2)) 3) (hc : c ∈ supportedChainSubmodule (sourceImage (n + 2)) 3) :
    classOperator n a c = 0 :=
  RelativeNormalizedThreeHomology.classOperator_supported _ _ _ c hc

theorem classOperator_boundary (n : ℕ) (a : sourceImage (n + 2))
    (c : Chains (Cylinder (n + 2)) 4) :
    classOperator n a (((singularComplex (Cylinder (n + 2))).d 4 3).hom c) = 0 :=
  RelativeNormalizedThreeHomology.classOperator_boundary _ _ _ c

theorem classOperator_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective (classOperator n a) :=
  RelativeNormalizedThreeHomology.classOperator_surjective _ _ _

theorem signed_faces (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 4, Cylinder (n + 2))) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val •
      RelativeSimplexCycles.homologyClass (sourceImage (n + 2)) 2
        (relativeTetrahedron n a (smp.comp (simplexFace 3 i)))) = 0 :=
  RelativeNormalizedThreeHomology.signed_faces (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a) smp

end NoExoticSixSphere.JamesSphere.PairNormalization
