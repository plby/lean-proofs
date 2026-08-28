import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometryFaces
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometryBoundary
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic

/-!
# Coherent simplex homotopies on the shared and outside cube faces

Adjacent swaps identify the actual common simplex faces. On the outside
faces, a native generalized loop is constant, so a lower-dimensional
homotopy fixing the constant simplex fixes those faces at every time.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeGluing

open FirstHurewicz SingularMayerVietoris CubeTriangulation
open SecondHurewicz.SimplyConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

theorem cubeOriginal_verticesBased (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) :
    VerticesBased x (n + 1) (p.val.comp (cubeSimplex e)) := by
  intro k
  change p (cubeSimplex e (stdVertices (n + 1) k)) = x
  rw [cubeSimplex_vertex]
  apply GenLoop.boundary p
  refine ⟨0, ?_⟩
  change (if (e.symm 0).val < k.val then (1 : I) else 0) = 0 ∨
    (if (e.symm 0).val < k.val then (1 : I) else 0) = 1
  split_ifs <;> simp

theorem cubeOriginal_face_zero (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (cubeSimplex e)).comp (simplexFace n 0) =
      ContinuousMap.const (Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (cubeSimplex_face_zero_boundary e s)

theorem cubeOriginal_face_last (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (cubeSimplex e)).comp (simplexFace n (Fin.last (n + 1))) =
      ContinuousMap.const (Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (cubeSimplex_face_last_boundary e s)

theorem cubeOriginal_face_swap (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (p.val.comp (cubeSimplex e)).comp (simplexFace n i.succ.castSucc) =
      (p.val.comp (cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e))).comp
        (simplexFace n i.succ.castSucc) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(Simplex n, CubeN (n + 1)) => p.val.comp f)
      (cubeSimplex_face_swap e i)

variable (H₀ : C(Simplex n, X) → C(I × Simplex n, X))
  (H₁ : C(Simplex (n + 1), X) → C(I × Simplex (n + 1), X))
  (hface : FaceCompatibleHomotopies n H₀ H₁)

include hface

theorem coherentCubeCell_face (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2)) (r : I) (s : Simplex n) :
    H₁ (p.val.comp (cubeSimplex e)) (r, simplexFace n i s) =
      H₀ ((p.val.comp (cubeSimplex e)).comp (simplexFace n i)) (r, s) :=
  DFunLike.congr_fun (hface (p.val.comp (cubeSimplex e)) i) (r, s)

theorem coherentCubeCell_swap (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (r : I) (s : Simplex (n + 1)) (hs : s i.succ.castSucc = 0) :
    H₁ (p.val.comp (cubeSimplex e)) (r, s) =
      H₁ (p.val.comp (cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e))) (r, s) := by
  let t := simplexFaceInverse n i.succ.castSucc ⟨s, hs⟩
  have ht : simplexFace n i.succ.castSucc t = s :=
    simplexFace_inverse n i.succ.castSucc ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₀ H₁ hface, coherentCubeCell_face H₀ H₁ hface,
    cubeOriginal_face_swap]

/-- The entire original cube boundary is fixed on every cell at every time. -/
theorem coherentCubeCell_boundary
    (hconst : H₀ (ContinuousMap.const (Simplex n) x) = ContinuousMap.const (I × Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1)))
    (r : I) (s : Simplex (n + 1)) (hs : cubeSimplex e s ∈ Cube.boundary (Fin (n + 1))) :
    H₁ (p.val.comp (cubeSimplex e)) (r, s) = x := by
  rcases (cubeSimplex_mem_boundary_iff e s).mp hs with hs | hs
  · let t := simplexFaceInverse n 0 ⟨s, hs⟩
    have ht : simplexFace n 0 t = s := simplexFace_inverse n 0 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_zero, hconst]
    rfl
  · let t := simplexFaceInverse n (Fin.last (n + 1)) ⟨s, hs⟩
    have ht : simplexFace n (Fin.last (n + 1)) t = s :=
      simplexFace_inverse n (Fin.last (n + 1)) ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_last, hconst]
    rfl

end Wikipedia.HopfProblem.HigherHurewicz.CubeGluing
