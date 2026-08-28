import Wikipedia.NoExoticSixSphere.FourSimplexFiberApex
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic

/-!
# The signed four-face relation for the actual fiber classes

The common-apex boundary lifts already cancel. Faces retaining the first
vertex have exactly the canonical cone apex. The exceptional face has
the second vertex as its canonical apex; a basepoint-valued edge path
identifies these two apex choices in actual fiber homology.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.FourSimplexBoundaryFiber

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  (smp : C(Simplex 4, X))
  (hU : ∀ i : Fin 5, ∀ s : SimplexBoundary 3, smp (simplexFace 3 i s.val) ∈ U)

theorem faceLift_canonical (i : Fin 5)
    (hv : smp (simplexFace 3 i (stdSimplex.vertex (S := ℝ) (0 : Fin 4))) = a.val) :
    faceLift U a smp hU (simplexFace 3 i (stdSimplex.vertex 0)) hv i =
      RelativeBoundaryFiberClass.lift U a 3 (faceSimplex U smp hU i)
        (stdSimplex.vertex 0) hv := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext t
    exact (congrArg smp (SimplexVertexCone.segment_face 3 i t s.val
      (stdSimplex.vertex 0))).symm

theorem faceClass_canonical (i : Fin 5)
    (hv : smp (simplexFace 3 i (stdSimplex.vertex (S := ℝ) (0 : Fin 4))) = a.val) :
    faceClass U a smp hU (simplexFace 3 i (stdSimplex.vertex 0)) hv i =
      RelativeSimplexFiberClass.fiberClass U a 0 (faceSimplex U smp hU i) hv := by
  unfold faceClass
  rw [faceLift_canonical]
  exact RelativeBoundaryFiberClass.homologyClass_firstVertex U a 0 _ hv

theorem faceClass_succ (hV : VerticesBased a.val 4 smp) (i : Fin 4) :
    faceClass U a smp hU (stdSimplex.vertex 0) (hV 0) i.succ =
      RelativeSimplexFiberClass.fiberClass U a 0 (faceSimplex U smp hU i.succ)
        (hV.face i.succ 0) := by
  have hv : simplexFace 3 i.succ (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) =
      stdSimplex.vertex (S := ℝ) (0 : Fin 5) := by
    rw [simplexFace_vertex]
    simp
  simpa only [hv] using faceClass_canonical U a smp hU i.succ
    (show smp (simplexFace 3 i.succ (stdSimplex.vertex 0)) = a.val by rw [hv]; exact hV 0)

theorem faceClass_zero (hV : VerticesBased a.val 4 smp) :
    faceClass U a smp hU (stdSimplex.vertex 1) (hV 1) 0 =
      RelativeSimplexFiberClass.fiberClass U a 0 (faceSimplex U smp hU 0) (hV.face 0 0) := by
  have hv : simplexFace 3 0 (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) =
      stdSimplex.vertex (S := ℝ) (1 : Fin 5) := by
    rw [simplexFace_vertex]
    rfl
  simpa only [hv] using faceClass_canonical U a smp hU 0
    (show smp (simplexFace 3 0 (stdSimplex.vertex 0)) = a.val by rw [hv]; exact hV 1)

theorem sum_fiberClass (hV : VerticesBased a.val 4 smp)
    (P : Path (stdSimplex.vertex (S := ℝ) (0 : Fin 5)) (stdSimplex.vertex (S := ℝ) (1 : Fin 5)))
    (hP : ∀ r, smp (P r) = a.val) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val •
      RelativeSimplexFiberClass.fiberClass U a 0 (faceSimplex U smp hU i) (hV.face i 0)) = 0 := by
  have he (i : Fin 5) : faceClass U a smp hU (stdSimplex.vertex 0) (hV 0) i =
      RelativeSimplexFiberClass.fiberClass U a 0 (faceSimplex U smp hU i) (hV.face i 0) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (faceClass_apex U a smp hU (hV 0) (hV 1) P hP 0).trans
        (faceClass_zero U a smp hU hV)
    · exact faceClass_succ U a smp hU hV j
  simpa only [he] using sum_faceClass U a smp hU (stdSimplex.vertex 0) (hV 0)

end NoExoticSixSphere.FourSimplexBoundaryFiber
