import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberClasses
import Wikipedia.NoExoticSixSphere.FourSimplexFiberFaceRelation

/-!
# The actual normalized fiber-class assignment kills four-boundaries

The coherent endpoint has subspace-valued two-faces and a constant
first edge. Its actual edge path supplies the apex comparison in the
proved four-face relation. Linearity then annihilates the original
singular four-boundary operator.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeNormalizedFiberClasses

def firstEdge : C(Simplex 1, Simplex 4) :=
  (simplexFace 3 4).comp ((simplexFace 2 3).comp (simplexFace 1 2))

theorem firstEdge_vertex_zero :
    firstEdge (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) =
      stdSimplex.vertex (S := ℝ) (0 : Fin 5) := by
  change simplexFace 3 4 (simplexFace 2 3 (simplexFace 1 2 (stdSimplex.vertex 0))) = _
  rw [simplexFace_vertex, simplexFace_vertex, simplexFace_vertex]
  congr 1

theorem firstEdge_vertex_one :
    firstEdge (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) =
      stdSimplex.vertex (S := ℝ) (1 : Fin 5) := by
  change simplexFace 3 4 (simplexFace 2 3 (simplexFace 1 2 (stdSimplex.vertex 1))) = _
  rw [simplexFace_vertex, simplexFace_vertex, simplexFace_vertex]
  congr 1

def firstEdgePath :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 5)) (stdSimplex.vertex (S := ℝ) (1 : Fin 5)) :=
  (simplexPath firstEdge).cast firstEdge_vertex_zero.symm firstEdge_vertex_one.symm

theorem firstEdgePath_apply (r : I) :
    firstEdgePath r = firstEdge (stdSimplexHomeomorphUnitInterval.symm r) := rfl

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

open RelativeTwoSkeletonNormalization

theorem endpoint_firstEdge (smp : C(Simplex 4, X)) :
    (endpoint U a hπ 4 smp).comp firstEdge = ContinuousMap.const (Simplex 1) a.val := by
  change (((endpoint U a hπ 4 smp).comp (simplexFace 3 4)).comp
    (simplexFace 2 3)).comp (simplexFace 1 2) = _
  rw [endpoint_face, endpoint_face, endpoint_face, endpoint_edge]

theorem endpoint_firstEdgePath (smp : C(Simplex 4, X)) (r : I) :
    endpoint U a hπ 4 smp (firstEdgePath r) = a.val :=
  congrArg (fun f : C(Simplex 1, X) ↦ f (stdSimplexHomeomorphUnitInterval.symm r))
    (endpoint_firstEdge U a hπ smp)

theorem endpoint_face_boundary (smp : C(Simplex 4, X)) (i : Fin 5) (s : SimplexBoundary 3) :
    endpoint U a hπ 4 smp (simplexFace 3 i s.val) ∈ U := by
  change ((endpoint U a hπ 4 smp).comp (simplexFace 3 i)) s.val ∈ U
  rw [endpoint_face]
  exact endpoint_tetrahedron_boundary U a hπ (smp.comp (simplexFace 3 i)) s.val s.property

theorem signed_faces (smp : C(Simplex 4, X)) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val • simplexClass U a hπ (smp.comp (simplexFace 3 i))) = 0 := by
  let τ := endpoint U a hπ 4 smp
  have hU := endpoint_face_boundary U a hπ smp
  have hV := endpoint_verticesBased U a hπ 4 smp
  have he (i : Fin 5) :
      RelativeSimplexFiberClass.fiberClass U a 0
        (FourSimplexBoundaryFiber.faceSimplex U τ hU i) (hV.face i 0) =
          simplexClass U a hπ (smp.comp (simplexFace 3 i)) := by
    have hs : FourSimplexBoundaryFiber.faceSimplex U τ hU i =
        RelativeNormalizedThreeHomology.relativeSimplex U a hπ
          (smp.comp (simplexFace 3 i)) := by
      apply Subtype.ext
      exact endpoint_face U a hπ 3 smp i
    unfold simplexClass
    congr 1
  simpa only [he] using FourSimplexBoundaryFiber.sum_fiberClass U a τ hU hV firstEdgePath
    (endpoint_firstEdgePath U a hπ smp)

theorem classOperator_boundary (c : Chains X 4) :
    classOperator U a hπ (((singularComplex X).d 4 3).hom c) = 0 := by
  have he : (classOperator U a hπ).comp ((singularComplex X).d 4 3).hom = 0 := by
    apply chainMap_ext X 4
    intro smp
    simpa only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      classOperator_simplex, LinearMap.zero_apply] using signed_faces U a hπ smp
  exact LinearMap.congr_fun he c

end NoExoticSixSphere.RelativeNormalizedFiberClasses
