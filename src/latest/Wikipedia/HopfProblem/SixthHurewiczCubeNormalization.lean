import Wikipedia.HopfProblem.SixthHurewiczNormalization
import Wikipedia.HopfProblem.HigherHurewiczCubeNormalization

/-!
# Actual sixth-cube normalization relative to its entire boundary

The proved all-dimensional finite-simplex gluing pastes the actual
complete homotopies over the native six-cube. The terminal cube has
exactly the normalized original simplex restrictions and is based on
every internal coordinate-equality hyperplane.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The genuine terminal native six-loop produced by coherent simplex pasting. -/
def normalizedCube (p : GenLoop (Fin 6) X x) : GenLoop (Fin 6) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) p

theorem normalizedCube_cell (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 6)) :
    (normalizedCube x p).val.comp (cubeSimplex e) =
      (normalizedSixSimplex x (p.val.comp (cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell
    (normalizationFiveSimplexHomotopy x) (normalizationSixSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationFiveSimplexHomotopy_const x) p e

/-- A genuine continuous homotopy fixing every point of the original six-cube boundary. -/
def normalizationCubeHomotopy (p : GenLoop (Fin 6) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 6)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) (normalizationSixSimplexHomotopy_zero x) p

theorem normalizationCube_homotopic (p : GenLoop (Fin 6) X x) :
    GenLoop.Homotopic p (normalizedCube x p) :=
  ⟨normalizationCubeHomotopy x p⟩

theorem normalizationCube_quotient (p : GenLoop (Fin 6) X x) :
    (⟦p⟧ : π_ 6 X x) = ⟦normalizedCube x p⟧ :=
  Quotient.sound (normalizationCube_homotopic x p)

theorem normalizedCube_cell_boundary (p : GenLoop (Fin 6) X x)
    (e : Equiv.Perm (Fin 6)) (s : Simplex 6) (hs : s ∈ sixSimplexBoundary) :
    normalizedCube x p (cubeSimplex e s) = x :=
  HigherHurewicz.coherentCubeEndpoint_cell_boundary
    (normalizationFiveSimplexHomotopy x) (normalizationSixSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationFiveSimplexHomotopy_const x)
    (normalizationFiveSimplexHomotopy_endpoint x) p e s hs

/-- All actual internal coordinate-equality hyperplanes of the terminal cube are based. -/
theorem normalizedCube_internalBased (p : GenLoop (Fin 6) X x)
    (u : Fin 6 → I) (i j : Fin 6) (hij : i ≠ j) (hu : u i = u j) :
    normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased
    (normalizationFiveSimplexHomotopy x) (normalizationSixSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationFiveSimplexHomotopy_const x)
    (normalizationFiveSimplexHomotopy_endpoint x) p u i j hij hu

end Wikipedia.HopfProblem.SixthHurewicz
