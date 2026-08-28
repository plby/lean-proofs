import Wikipedia.HopfProblem.FourthHurewiczNormalization
import Wikipedia.HopfProblem.HigherHurewiczCubeNormalization

/-!
# Actual fourth-cube normalization relative to the whole boundary

The complete simplex homotopies paste over the genuine permutation
triangulation of the native four-cube. The resulting native loop is
homotopic to the original loop relative to its full boundary, restricts
to the exact normalized four-simplices, and is based on every internal
coordinate-equality hyperplane.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The genuine terminal native four-loop obtained by coherent simplex pasting. -/
def normalizedCube (p : GenLoop (Fin 4) X x) : GenLoop (Fin 4) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) p

/-- The prescribed endpoint on every original permutation simplex is literal. -/
theorem normalizedCube_cell (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 4)) :
    (normalizedCube x p).val.comp (cubeSimplex e) =
      (normalizedFourSimplex x (p.val.comp (cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell
    (normalizationThreeSimplexHomotopy x) (normalizationFourSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationThreeSimplexHomotopy_const x) p e

/-- A genuine continuous homotopy fixing every point of the original cube boundary. -/
def normalizationCubeHomotopy (p : GenLoop (Fin 4) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 4)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) (normalizationFourSimplexHomotopy_zero x) p

theorem normalizationCube_homotopic (p : GenLoop (Fin 4) X x) :
    GenLoop.Homotopic p (normalizedCube x p) :=
  ⟨normalizationCubeHomotopy x p⟩

/-- Equality holds in Mathlib's original native fourth homotopy quotient. -/
theorem normalizationCube_quotient (p : GenLoop (Fin 4) X x) :
    (⟦p⟧ : π_ 4 X x) = ⟦normalizedCube x p⟧ :=
  Quotient.sound (normalizationCube_homotopic x p)

theorem normalizedCube_cell_boundary (p : GenLoop (Fin 4) X x)
    (e : Equiv.Perm (Fin 4)) (s : Simplex 4) (hs : s ∈ fourSimplexBoundary) :
    normalizedCube x p (cubeSimplex e s) = x :=
  HigherHurewicz.coherentCubeEndpoint_cell_boundary
    (normalizationThreeSimplexHomotopy x) (normalizationFourSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationThreeSimplexHomotopy_const x)
    (normalizationThreeSimplexHomotopy_endpoint x) p e s hs

/-- All original internal equal-coordinate hyperplanes are genuinely based. -/
theorem normalizedCube_internalBased (p : GenLoop (Fin 4) X x)
    (u : Fin 4 → I) (i j : Fin 4) (hij : i ≠ j) (hu : u i = u j) :
    normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased
    (normalizationThreeSimplexHomotopy x) (normalizationFourSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationThreeSimplexHomotopy_const x)
    (normalizationThreeSimplexHomotopy_endpoint x) p u i j hij hu

end Wikipedia.HopfProblem.FourthHurewicz
