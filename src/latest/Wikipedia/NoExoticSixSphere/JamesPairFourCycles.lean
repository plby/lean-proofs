import Wikipedia.NoExoticSixSphere.JamesPairFiberDetection
import Wikipedia.NoExoticSixSphere.RelativeThreeSkeletonNormalization
import Wikipedia.NoExoticSixSphere.RelativeNormalizedHomology

/-!
# Normalized four-simplices for the original James cylinder pair

All fiber-connectivity and native third-homotopy surjectivity inputs are
discharged. The actual coherent family compresses tetrahedra into the
source and gives relative four-cycles. These cycles represent the original
fourth relative homology and satisfy the original signed five-boundary
relation. Third fiber homology vanishing is not inferred here.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization

open ComparisonCylinder

attribute [local instance] PairNormalization.cylinderSimplyConnected
attribute [local instance] PairNormalization.sourceSimplyConnected

local instance fiberSimplyConnected (n : ℕ) (a : sourceImage (n + 2)) :
    SimplyConnectedSpace (RelativeFiberHomology.Fiber (sourceImage (n + 2)) a) :=
  sourceFiber_simplyConnected n a

local instance fiberPiTwo (n : ℕ) (a : sourceImage (n + 2)) :
    Subsingleton (π_ 2 (RelativeFiberHomology.Fiber (sourceImage (n + 2)) a)
      (HomotopyFiber.basepoint (subtypeInclusion (sourceImage (n + 2))) a)) :=
  PairNormalization.fiber_piTwo_subsingleton n a (sourceFiberBasepoint (n + 2) a)

def homotopy (n d : ℕ) (a : sourceImage (n + 2)) (smp : C(Simplex d, Cylinder (n + 2))) :
    C(I × Simplex d, Cylinder (n + 2)) :=
  RelativeThreeSkeletonNormalization.homotopy (sourceImage (n + 2)) a
    (PairNormalization.inclusion_piThree_surjective n)
    (PairNormalization.inclusion_piTwo_surjective n a) d smp

theorem homotopy_zero (n d : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex d, Cylinder (n + 2))) (s : Simplex d) :
    homotopy n d a smp (0, s) = smp s :=
  RelativeThreeSkeletonNormalization.homotopy_zero _ _ _ _ d smp s

theorem homotopy_face (n d : ℕ) (a : sourceImage (n + 2)) :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies d
      (homotopy n d a) (homotopy n (d + 1) a) :=
  RelativeThreeSkeletonNormalization.homotopy_face _ _ _ _ d

theorem homotopy_mem (n d : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex d, Cylinder (n + 2))) (hs : ∀ s, smp s ∈ sourceImage (n + 2))
    (p : I × Simplex d) : homotopy n d a smp p ∈ sourceImage (n + 2) :=
  RelativeThreeSkeletonNormalization.homotopy_mem _ _ _ _ d smp hs p

def endpoint (n d : ℕ) (a : sourceImage (n + 2)) (smp : C(Simplex d, Cylinder (n + 2))) :
    C(Simplex d, Cylinder (n + 2)) :=
  SecondHurewicz.SimplyConnected.timeSlice (homotopy n d a smp) 1

theorem endpoint_tetrahedron_mem (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 3, Cylinder (n + 2))) (s : Simplex 3) :
    endpoint n 3 a smp s ∈ sourceImage (n + 2) :=
  RelativeThreeSkeletonNormalization.endpoint_tetrahedron_mem _ _ _ _ smp s

theorem endpoint_fourSimplex_boundary (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 4, Cylinder (n + 2))) (s : Simplex 4)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary 4) :
    endpoint n 4 a smp s ∈ sourceImage (n + 2) :=
  RelativeThreeSkeletonNormalization.endpoint_fourSimplex_boundary _ _ _ _ smp s hs

def relativeSimplex (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 4, Cylinder (n + 2))) :
    RelativeSimplexCycles.RelativeSimplex (sourceImage (n + 2)) 4 :=
  ⟨endpoint n 4 a smp, endpoint_fourSimplex_boundary n a smp⟩

def classOperator (n : ℕ) (a : sourceImage (n + 2)) :
    Chains (Cylinder (n + 2)) 4 →ₗ[ℤ] RelativeSingularHomology.Homology (sourceImage (n + 2)) 4 :=
  RelativeNormalizedHomology.classOperator (sourceImage (n + 2)) 3
    (fun d ↦ homotopy n d a) (endpoint_fourSimplex_boundary n a)

theorem classOperator_simplex (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 4, Cylinder (n + 2))) :
    classOperator n a (simplexChain (Cylinder (n + 2)) 4 smp) =
      RelativeSimplexCycles.homologyClass (sourceImage (n + 2)) 3 (relativeSimplex n a smp) :=
  RelativeNormalizedHomology.classOperator_simplex _ _ _ _ smp

theorem classOperator_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective (classOperator n a) :=
  RelativeNormalizedHomology.classOperator_surjective _ _ _ _
    (fun d ↦ homotopy_zero n d a) (fun d ↦ homotopy_face n d a) (fun d ↦ homotopy_mem n d a)

theorem classOperator_boundary (n : ℕ) (a : sourceImage (n + 2))
    (c : Chains (Cylinder (n + 2)) 5) :
    classOperator n a (((singularComplex (Cylinder (n + 2))).d 5 4).hom c) = 0 :=
  RelativeNormalizedHomology.classOperator_boundary _ _ _ _ (fun d ↦ homotopy_face n d a) c

theorem signed_faces (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 5, Cylinder (n + 2))) :
    (∑ i : Fin 6, (-1 : ℤ) ^ i.val • RelativeSimplexCycles.homologyClass
      (sourceImage (n + 2)) 3 (relativeSimplex n a (smp.comp (simplexFace 4 i)))) = 0 :=
  RelativeNormalizedHomology.signed_faces _ _ _ _ (fun d ↦ homotopy_face n d a) smp

end NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization
