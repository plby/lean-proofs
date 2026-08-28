import Wikipedia.NoExoticSixSphere.RelativeNormalizationData
import Wikipedia.NoExoticSixSphere.SimplexBoundaryFiber
import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberPairHomotopy

/-!
# The actual normalized fiber assignment in every degree

A coherent normalization gives actual relative simplex classes and
actual cone-path fiber classes. The latter vanish on subspace chains
and on the original differential, by the all-degree signed face relation.
The raw-simplex formula follows from the actual pair homotopy.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeNormalization.Data

open RelativeFiberHomology RelativeSimplexCycles

variable {X : Type} [TopologicalSpace X] {U : Set X} {a : U} {n : ℕ} (D : Data U a n)

def relativeSimplex (smp : C(Simplex (n + 3), X)) : RelativeSimplex U (n + 3) :=
  ⟨D.endpoint (n + 3) smp, D.endpoint_boundary smp⟩

def relativeClassOperator : Chains X (n + 3) →ₗ[ℤ] RelativeSingularHomology.Homology U (n + 3) :=
  RelativeNormalizedHomology.classOperator U (n + 2) D.homotopy D.endpoint_boundary

theorem relativeClassOperator_simplex (smp : C(Simplex (n + 3), X)) :
    D.relativeClassOperator (simplexChain X (n + 3) smp) =
      homologyClass U (n + 2) (D.relativeSimplex smp) :=
  RelativeNormalizedHomology.classOperator_simplex _ _ _ _ smp

theorem relativeClassOperator_surjective : Function.Surjective D.relativeClassOperator :=
  RelativeNormalizedHomology.classOperator_surjective _ _ _ _ D.initial D.face D.preserves

def simplexFiberClass (smp : C(Simplex (n + 3), X)) : SingularHomology (Fiber U a) (n + 2) :=
  RelativeSimplexFiberClass.fiberClass U a n (D.relativeSimplex smp) (D.vertices (n + 3) smp 0)

def fiberClassOperator : Chains X (n + 3) →ₗ[ℤ] SingularHomology (Fiber U a) (n + 2) :=
  chainLift X (n + 3) D.simplexFiberClass

theorem fiberClassOperator_simplex (smp : C(Simplex (n + 3), X)) :
    D.fiberClassOperator (simplexChain X (n + 3) smp) = D.simplexFiberClass smp :=
  chainLift_simplex X (n + 3) _ smp

theorem simplexFiberClass_eq_zero_of_mem (smp : C(Simplex (n + 3), X)) (hs : ∀ s, smp s ∈ U) :
    D.simplexFiberClass smp = 0 :=
  RelativeSimplexFiberClass.fiberClass_eq_zero_of_mem U a n _ _ (D.endpoint_mem (n + 3) smp hs)

theorem fiberClassOperator_supported (c : Chains X (n + 3))
    (hc : c ∈ supportedChainSubmodule U (n + 3)) : D.fiberClassOperator c = 0 := by
  have hle : supportedChainSubmodule U (n + 3) ≤ LinearMap.ker D.fiberClassOperator := by
    rw [supportedChainSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨smp, hs, rfl⟩
    change D.fiberClassOperator (simplexChain X (n + 3) smp) = 0
    rw [fiberClassOperator_simplex]
    exact D.simplexFiberClass_eq_zero_of_mem smp (fun s ↦ hs ⟨s, rfl⟩)
  exact hle hc

theorem endpoint_face_boundary (smp : C(Simplex (n + 4), X)) (i : Fin (n + 5))
    (s : SimplexBoundary (n + 3)) : D.endpoint (n + 4) smp (simplexFace (n + 3) i s.val) ∈ U := by
  change ((D.endpoint (n + 4) smp).comp (simplexFace (n + 3) i)) s.val ∈ U
  rw [D.endpoint_face]
  exact D.endpoint_boundary (smp.comp (simplexFace (n + 3) i)) s.val s.property

theorem fiber_signed_faces (smp : C(Simplex (n + 4), X)) :
    (∑ i : Fin (n + 5), (-1 : ℤ) ^ i.val •
      D.simplexFiberClass (smp.comp (simplexFace (n + 3) i))) = 0 := by
  let τ := D.endpoint (n + 4) smp
  have hU := D.endpoint_face_boundary smp
  have hV := D.vertices (n + 4) smp
  have he (i : Fin (n + 5)) : RelativeSimplexFiberClass.fiberClass U a n
      (SimplexBoundaryFiber.faceSimplex U n τ hU i) (hV.face i 0) =
        D.simplexFiberClass (smp.comp (simplexFace (n + 3) i)) := by
    have hs : SimplexBoundaryFiber.faceSimplex U n τ hU i =
        D.relativeSimplex (smp.comp (simplexFace (n + 3) i)) := by
      apply Subtype.ext
      exact D.endpoint_face (n + 3) smp i
    unfold simplexFiberClass
    congr 1
  simpa only [he] using SimplexBoundaryFiber.sum_fiberClass U a n τ hU hV
    (SimplexFirstEdge.path (n + 3)) (D.endpoint_firstEdgePath smp)

theorem fiberClassOperator_boundary (c : Chains X (n + 4)) :
    D.fiberClassOperator (((singularComplex X).d (n + 4) (n + 3)).hom c) = 0 := by
  have he : D.fiberClassOperator.comp ((singularComplex X).d (n + 4) (n + 3)).hom = 0 := by
    apply chainMap_ext X (n + 4)
    intro smp
    simpa only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      fiberClassOperator_simplex, LinearMap.zero_apply] using D.fiber_signed_faces smp
  exact LinearMap.congr_fun he c

theorem simplexFiberClass_eq_fiberClass (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    D.simplexFiberClass smp.val = RelativeSimplexFiberClass.fiberClass U a n smp hv :=
  RelativeSimplexFiberClass.fiberClass_eq_of_pairHomotopy U a n smp
    (D.relativeSimplex smp.val) hv (D.vertices (n + 3) smp.val 0)
    (D.pairHomotopy (n + 3) smp.val) (D.homotopy_boundary (n + 2) smp.val smp.property)
    (D.homotopy_vertex (n + 3) smp.val 0 hv)

end NoExoticSixSphere.RelativeNormalization.Data
