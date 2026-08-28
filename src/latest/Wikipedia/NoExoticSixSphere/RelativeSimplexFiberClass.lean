import Wikipedia.NoExoticSixSphere.RelativeFiberSubspacePaths
import Wikipedia.NoExoticSixSphere.RelativeContractibleSubspace
import Wikipedia.NoExoticSixSphere.RelativeSimplexCycles
import Wikipedia.NoExoticSixSphere.SimplexVertexCone

/-!
# Actual fiber-homology classes of relative simplices with a based first vertex

Cone paths from the opposite face to the first vertex give a simplex
in the original inclusion fiber. Its boundary lies in the contractible
subspace of paths wholly in the source. The proved absolute-to-relative
isomorphism therefore gives an actual fiber-homology class. No face
relation or inverse-to-transgression assertion is assumed here.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected OrbitPair

namespace NoExoticSixSphere.RelativeSimplexFiberClass

open RelativeSingularHomology RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def oppositeFace (n : ℕ) (smp : RelativeSimplex U (n + 1)) : C(Simplex n, U) :=
  ⟨fun s ↦ ⟨smp.val (simplexFace n 0 s),
    smp.property _ (simplexFace_mem_boundary n 0 s)⟩,
    (smp.val.continuous.comp (simplexFace n 0).continuous).subtype_mk _⟩

def coneHomotopy (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val) :
    ((subtypeInclusion U).comp (oppositeFace U n smp)).Homotopy
      (ContinuousMap.const (Simplex n) a.val) where
  toContinuousMap := smp.val.comp (SimplexVertexCone.cone n)
  map_zero_left s := congrArg smp.val (SimplexVertexCone.cone_zero n s)
  map_one_left s := (congrArg smp.val (SimplexVertexCone.cone_one n s)).trans hv

def liftedSimplex (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val) :
    C(Simplex n, Fiber U a) :=
  HomotopyFiber.lift (subtypeInclusion U) a.val (oppositeFace U n smp)
    (coneHomotopy U a n smp hv)

theorem liftedSimplex_path (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (s : Simplex n) (t : I) :
    (liftedSimplex U a n smp hv s).val.2 t = smp.val (SimplexVertexCone.cone n (t, s)) := rfl

theorem liftedSimplex_boundary (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (s : Simplex n) (hs : s ∈ simplexBoundary n) :
    liftedSimplex U a n smp hv s ∈ RelativeFiberSubspacePaths.subspace U a := by
  intro t
  exact smp.property _ (SimplexVertexCone.cone_boundary n t s hs)

theorem liftedSimplex_mem (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (hU : ∀ s, smp.val s ∈ U) (s : Simplex n) :
    liftedSimplex U a n smp hv s ∈ RelativeFiberSubspacePaths.subspace U a :=
  fun t ↦ hU (SimplexVertexCone.cone n (t, s))

def relativeSimplex (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val) :
    RelativeSimplex (RelativeFiberSubspacePaths.subspace U a) n :=
  ⟨liftedSimplex U a n smp hv, liftedSimplex_boundary U a n smp hv⟩

def fiberHomologyEquiv (n : ℕ) :
    SingularHomology (Fiber U a) (n + 2) ≃ₗ[ℤ]
      Homology (RelativeFiberSubspacePaths.subspace U a) (n + 2) := by
  letI := RelativeFiberSubspacePaths.contractibleSpace U a
  exact contractibleSubspaceEquiv (RelativeFiberSubspacePaths.subspace U a) n

theorem fiberHomologyEquiv_apply (n : ℕ) (c : SingularHomology (Fiber U a) (n + 2)) :
    fiberHomologyEquiv U a n c =
      toRelative (RelativeFiberSubspacePaths.subspace U a) (n + 2) c := rfl

def fiberClass (n : ℕ) (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    SingularHomology (Fiber U a) (n + 2) :=
  (fiberHomologyEquiv U a n).symm
    (homologyClass (RelativeFiberSubspacePaths.subspace U a) (n + 1)
      (relativeSimplex U a (n + 2) smp hv))

theorem fiberClass_toRelative (n : ℕ) (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    toRelative (RelativeFiberSubspacePaths.subspace U a) (n + 2) (fiberClass U a n smp hv) =
      homologyClass (RelativeFiberSubspacePaths.subspace U a) (n + 1)
        (relativeSimplex U a (n + 2) smp hv) :=
  (fiberHomologyEquiv U a n).apply_symm_apply _

theorem fiberClass_eq_zero_of_mem (n : ℕ) (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val)
    (hU : ∀ s, smp.val s ∈ U) : fiberClass U a n smp hv = 0 := by
  have he : cycle (RelativeFiberSubspacePaths.subspace U a) (n + 1)
      (relativeSimplex U a (n + 2) smp hv) = 0 := by
    apply Subtype.ext
    apply (quotientMap_eq_zero_iff _ (n + 2) _).mpr
    apply simplexChain_mem_supported
    rintro _ ⟨s, rfl⟩
    exact liftedSimplex_mem U a (n + 2) smp hv hU s
  change (fiberHomologyEquiv U a n).symm
    (ModuleHomology.cycleClass _ (n + 2) (cycle _ (n + 1) _)) = 0
  rw [he, map_zero, map_zero]

end NoExoticSixSphere.RelativeSimplexFiberClass
