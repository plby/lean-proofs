import Wikipedia.NoExoticSixSphere.JamesPairRelativeCycles
import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberClasses

/-!
# Actual source-inclusion fiber classes for the original James cylinder pair

The construction uses the proved connectivity and second-homotopy
surjectivity of the original pair. Its values are actual fiber homology
classes. It vanishes on source-image chains, but descent through
four-boundaries and transgression injectivity are not asserted.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.PairNormalization

open ComparisonCylinder

attribute [local instance] cylinderSimplyConnected sourceSimplyConnected

def simplexFiberClass (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 3, Cylinder (n + 2))) : SingularHomology (SourceFiber (n + 2) a) 2 :=
  RelativeNormalizedFiberClasses.simplexClass (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a) smp

def fiberClassOperator (n : ℕ) (a : sourceImage (n + 2)) :
    Chains (Cylinder (n + 2)) 3 →ₗ[ℤ] SingularHomology (SourceFiber (n + 2) a) 2 :=
  RelativeNormalizedFiberClasses.classOperator (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a)

theorem fiberClassOperator_simplex (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 3, Cylinder (n + 2))) :
    fiberClassOperator n a (simplexChain (Cylinder (n + 2)) 3 smp) =
      simplexFiberClass n a smp :=
  RelativeNormalizedFiberClasses.classOperator_simplex _ _ _ smp

theorem fiberClassOperator_supported (n : ℕ) (a : sourceImage (n + 2))
    (c : Chains (Cylinder (n + 2)) 3) (hc : c ∈ supportedChainSubmodule (sourceImage (n + 2)) 3) :
    fiberClassOperator n a c = 0 :=
  RelativeNormalizedFiberClasses.classOperator_supported _ _ _ c hc

end NoExoticSixSphere.JamesSphere.PairNormalization
