import Wikipedia.HopfProblem.FifthHurewiczNormalization
import Wikipedia.HopfProblem.HigherHurewiczCubeNormalization

/-!
# Actual fifth-cube normalization relative to its entire boundary

The previously proved all-dimensional finite-simplex gluing pastes the
actual complete homotopies over the native five-cube. The terminal cube
has exactly the normalized original simplex restrictions and is based
on every internal coordinate-equality hyperplane.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The genuine terminal native five-loop produced by coherent simplex pasting. -/
def normalizedCube (p : GenLoop (Fin 5) X x) : GenLoop (Fin 5) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) p

theorem normalizedCube_cell (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 5)) :
    (normalizedCube x p).val.comp (cubeSimplex e) =
      (normalizedFiveSimplex x (p.val.comp (cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell
    (normalizationFourSimplexHomotopy x) (normalizationFiveSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationFourSimplexHomotopy_const x) p e

/-- A genuine continuous homotopy fixing every point of the original five-cube boundary. -/
def normalizationCubeHomotopy (p : GenLoop (Fin 5) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 5)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) (normalizationFiveSimplexHomotopy_zero x) p

theorem normalizationCube_homotopic (p : GenLoop (Fin 5) X x) :
    GenLoop.Homotopic p (normalizedCube x p) :=
  ⟨normalizationCubeHomotopy x p⟩

theorem normalizationCube_quotient (p : GenLoop (Fin 5) X x) :
    (⟦p⟧ : π_ 5 X x) = ⟦normalizedCube x p⟧ :=
  Quotient.sound (normalizationCube_homotopic x p)

theorem normalizedCube_cell_boundary (p : GenLoop (Fin 5) X x)
    (e : Equiv.Perm (Fin 5)) (s : Simplex 5) (hs : s ∈ fiveSimplexBoundary) :
    normalizedCube x p (cubeSimplex e s) = x :=
  HigherHurewicz.coherentCubeEndpoint_cell_boundary
    (normalizationFourSimplexHomotopy x) (normalizationFiveSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationFourSimplexHomotopy_const x)
    (normalizationFourSimplexHomotopy_endpoint x) p e s hs

/-- All actual internal coordinate-equality hyperplanes of the terminal cube are based. -/
theorem normalizedCube_internalBased (p : GenLoop (Fin 5) X x)
    (u : Fin 5 → I) (i j : Fin 5) (hij : i ≠ j) (hu : u i = u j) :
    normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased
    (normalizationFourSimplexHomotopy x) (normalizationFiveSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationFourSimplexHomotopy_const x)
    (normalizationFourSimplexHomotopy_endpoint x) p u i j hij hu

end Wikipedia.HopfProblem.FifthHurewicz
