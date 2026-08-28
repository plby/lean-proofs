import Wikipedia.HopfProblem.HigherHurewiczCubeGluing
import Wikipedia.HopfProblem.HigherHurewiczCubeNormalizationGeometry
import Wikipedia.HopfProblem.HigherHurewiczSimplexEndpointBoundary

/-!
# Coherent cube normalization fixes all internal permutation faces

If every lower-dimensional terminal simplex is constant, the genuinely
pasted native cube has all internal equal-coordinate hyperplanes based.
This is the geometric input to native cubical subdivision recovery in
arbitrary positive dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz CubeTriangulation SecondHurewicz.SimplyConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
  (H : SingularSimplex X n → C(I × Simplex n, X))
  (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
  (hface : FaceCompatibleHomotopies n H H')
  (hconst : H (ContinuousMap.const (Simplex n) x) =
    ContinuousMap.const (I × Simplex n) x)
  (hone : ∀ smp, timeSlice (H smp) 1 = ContinuousMap.const (Simplex n) x)

include hone

/-- Each original permutation simplex has its full boundary based after pasting. -/
theorem coherentCubeEndpoint_cell_boundary (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1))
    (hs : s ∈ simplexBoundary (n + 1)) :
    CubeGluing.coherentCubeEndpoint H H' hface hconst p (cubeSimplex e s) = x := by
  have he := congrArg (fun f : C(Simplex (n + 1), X) => f s)
    (CubeGluing.coherentCubeEndpoint_cell H H' hface hconst p e)
  exact he.trans (simplexEndpoint_boundary H H' hface x hone _ s hs)

/-- Every coordinate-equality hyperplane of the actual terminal native cube is based. -/
theorem coherentCubeEndpoint_internalBased (p : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → I) (i j : Fin (n + 1)) (hij : i ≠ j) (hu : u i = u j) :
    CubeGluing.coherentCubeEndpoint H H' hface hconst p u = x := by
  obtain ⟨e, s, rfl⟩ := exists_cubeSimplex u
  exact coherentCubeEndpoint_cell_boundary H H' hface hconst hone p e s
    (cubeSimplex_coordinate_equality_boundary e s hij hu)

end Wikipedia.HopfProblem.HigherHurewicz
