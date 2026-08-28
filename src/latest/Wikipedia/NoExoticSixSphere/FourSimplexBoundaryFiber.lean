import Wikipedia.NoExoticSixSphere.RelativeBoundaryFiberComparison
import Wikipedia.NoExoticSixSphere.SimplexBoundaryCancellation

/-!
# Coherent boundary lifts of the faces of one actual four-simplex

Only the two-faces must map into the source. Cone paths from all those
faces to one common apex give maps from tetrahedron boundaries into the
actual inclusion fiber. The original coface identities give exact
agreement, hence the signed sum of their actual homology classes is zero.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected OrbitPair

namespace NoExoticSixSphere.FourSimplexBoundaryFiber

open RelativeFiberHomology RelativeSimplexCycles

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  (smp : C(Simplex 4, X))
  (hU : ∀ i : Fin 5, ∀ s : SimplexBoundary 3, smp (simplexFace 3 i s.val) ∈ U)

def faceSimplex (i : Fin 5) : RelativeSimplex U 3 :=
  ⟨smp.comp (simplexFace 3 i), fun s hs ↦ hU i ⟨s, hs⟩⟩

def source (i : Fin 5) : C(SimplexBoundary 3, U) :=
  RelativeBoundaryFiberClass.source U 3 (faceSimplex U smp hU i)

def coneHomotopy (v : Simplex 4) (hv : smp v = a.val) (i : Fin 5) :
    ((subtypeInclusion U).comp (source U smp hU i)).Homotopy
      (ContinuousMap.const (SimplexBoundary 3) a.val) where
  toContinuousMap := smp.comp ((SimplexVertexCone.segment 4).comp
    ⟨fun p ↦ (p.1, (simplexFace 3 i p.2.val, v)),
      continuous_fst.prodMk (((simplexFace 3 i).continuous.comp
        (continuous_subtype_val.comp continuous_snd)).prodMk continuous_const)⟩)
  map_zero_left _ := congrArg smp (SimplexVertexCone.segment_zero 4 _ v)
  map_one_left _ := (congrArg smp (SimplexVertexCone.segment_one 4 _ v)).trans hv

def faceLift (v : Simplex 4) (hv : smp v = a.val) (i : Fin 5) :
    C(SimplexBoundary 3, Fiber U a) :=
  HomotopyFiber.lift (subtypeInclusion U) a.val (source U smp hU i)
    (coneHomotopy U a smp hU v hv i)

theorem faceLift_coface (v : Simplex 4) (hv : smp v = a.val) (i j : Fin 4) (hij : i ≤ j) :
    (faceLift U a smp hU v hv j.succ).comp (simplexFaceBoundary 2 i) =
      (faceLift U a smp hU v hv i.castSucc).comp (simplexFaceBoundary 2 j) := by
  apply ContinuousMap.ext
  intro s
  have he : simplexFace 3 j.succ (simplexFace 2 i s) =
      simplexFace 3 i.castSucc (simplexFace 2 j s) :=
    congrArg (fun f : C(Simplex 2, Simplex 4) ↦ f s)
      (PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij)
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (congrArg smp he)
  · ext t
    exact congrArg (fun z ↦ smp (SimplexVertexCone.segment 4 (t, (z, v)))) he

def faceClass (v : Simplex 4) (hv : smp v = a.val) (i : Fin 5) :
    SingularHomology (Fiber U a) 2 :=
  singularHomologyMap (faceLift U a smp hU v hv i) 2
    (ModuleHomology.cycleClass (singularComplex (SimplexBoundary 3)) 2
      (SimplexBoundaryChains.cycle 1))

theorem sum_faceClass (v : Simplex 4) (hv : smp v = a.val) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val • faceClass U a smp hU v hv i) = 0 :=
  SimplexBoundaryChains.four_homology_cancel (faceLift U a smp hU v hv)
    (faceLift_coface U a smp hU v hv)

end NoExoticSixSphere.FourSimplexBoundaryFiber
