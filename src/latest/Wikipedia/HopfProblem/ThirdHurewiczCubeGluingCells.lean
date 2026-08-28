import Wikipedia.HopfProblem.ThirdHurewiczCubeGluingBasic
import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCoverBoundary
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic

/-!
# Coherent homotopies on shared and outside tetrahedral faces

The actual coface identities give equality on each shared tetrahedral
face. On the outside faces, the original generalized loop is constant,
so a triangle homotopy fixing the constant triangle fixes those faces.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing

open FirstHurewicz SingularMayerVietoris Geometry CubeTriangulation
open SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X}

theorem cubeOriginal_verticesBased (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    VerticesBased x 3 (p.val.comp (cubeTetrahedron e)) := by
  intro k
  change p (cubeTetrahedron e (stdVertices 3 k)) = x
  rw [cubeTetrahedron_vertex]
  apply GenLoop.boundary p
  refine ⟨0, ?_⟩
  change (if (e.symm 0).val < k.val then (1 : I) else 0) = 0 ∨
    (if (e.symm 0).val < k.val then (1 : I) else 0) = 1
  split_ifs <;> simp

theorem cubeOriginal_face_zero (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (cubeTetrahedron e)).comp (simplexFace 2 0) =
      ContinuousMap.const (Simplex 2) x := by
  ext s
  exact GenLoop.boundary p _ (cubeTetrahedron_face_zero_boundary e s)

theorem cubeOriginal_face_three (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (cubeTetrahedron e)).comp (simplexFace 2 3) =
      ContinuousMap.const (Simplex 2) x := by
  ext s
  exact GenLoop.boundary p _ (cubeTetrahedron_face_three_boundary e s)

theorem cubeOriginal_face_one_swap (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (cubeTetrahedron e)).comp (simplexFace 2 1) =
      (p.val.comp (cubeTetrahedron ((Equiv.swap 0 1).trans e))).comp (simplexFace 2 1) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(Simplex 2, Cube3) => p.val.comp f) (cubeTetrahedron_face_one_swap e)

theorem cubeOriginal_face_two_swap (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (cubeTetrahedron e)).comp (simplexFace 2 2) =
      (p.val.comp (cubeTetrahedron ((Equiv.swap 1 2).trans e))).comp (simplexFace 2 2) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(Simplex 2, Cube3) => p.val.comp f) (cubeTetrahedron_face_two_swap e)

variable (H₂ : C(Simplex 2, X) → C(I × Simplex 2, X))
  (H₃ : C(Simplex 3, X) → C(I × Simplex 3, X))
  (hface : FaceCompatibleHomotopies 2 H₂ H₃)

include hface

theorem coherentCubeCell_face (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3))
    (i : Fin 4) (r : I) (s : Simplex 2) :
    H₃ (p.val.comp (cubeTetrahedron e)) (r, simplexFace 2 i s) =
      H₂ ((p.val.comp (cubeTetrahedron e)).comp (simplexFace 2 i)) (r, s) :=
  DFunLike.congr_fun (hface (p.val.comp (cubeTetrahedron e)) i) (r, s)

theorem coherentCubeCell_one_swap (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3))
    (r : I) (s : Simplex 3) (hs : s 1 = 0) :
    H₃ (p.val.comp (cubeTetrahedron e)) (r, s) =
      H₃ (p.val.comp (cubeTetrahedron ((Equiv.swap 0 1).trans e))) (r, s) := by
  let t := simplexFaceInverse 2 1 ⟨s, hs⟩
  have ht : simplexFace 2 1 t = s := simplexFace_inverse 2 1 ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₂ H₃ hface, coherentCubeCell_face H₂ H₃ hface,
    cubeOriginal_face_one_swap]

theorem coherentCubeCell_two_swap (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3))
    (r : I) (s : Simplex 3) (hs : s 2 = 0) :
    H₃ (p.val.comp (cubeTetrahedron e)) (r, s) =
      H₃ (p.val.comp (cubeTetrahedron ((Equiv.swap 1 2).trans e))) (r, s) := by
  let t := simplexFaceInverse 2 2 ⟨s, hs⟩
  have ht : simplexFace 2 2 t = s := simplexFace_inverse 2 2 ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₂ H₃ hface, coherentCubeCell_face H₂ H₃ hface,
    cubeOriginal_face_two_swap]

/-- Every point on the cube perimeter is fixed, including points lying on several cells. -/
theorem coherentCubeCell_boundary
    (hconst : H₂ (ContinuousMap.const (Simplex 2) x) = ContinuousMap.const (I × Simplex 2) x)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : I) (s : Simplex 3)
    (hs : cubeTetrahedron e s ∈ Cube.boundary (Fin 3)) :
    H₃ (p.val.comp (cubeTetrahedron e)) (r, s) = x := by
  rcases (cubeTetrahedron_mem_boundary_iff e s).mp hs with hs | hs
  · let t := simplexFaceInverse 2 0 ⟨s, hs⟩
    have ht : simplexFace 2 0 t = s := simplexFace_inverse 2 0 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₂ H₃ hface, cubeOriginal_face_zero, hconst]
    rfl
  · let t := simplexFaceInverse 2 3 ⟨s, hs⟩
    have ht : simplexFace 2 3 t = s := simplexFace_inverse 2 3 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₂ H₃ hface, cubeOriginal_face_three, hconst]
    rfl

end Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing
