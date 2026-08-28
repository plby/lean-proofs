import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Normalization
import Wikipedia.HopfProblem.HigherHurewiczCubeNormalization

/-!
# Actual seventh-cube normalization relative to its entire boundary

The proved all-dimensional finite-simplex gluing pastes the actual
complete homotopies over the native seven-cube. The terminal cube has
exactly the normalized original simplex restrictions and is based on
every internal coordinate-equality hyperplane.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The genuine terminal native seven-loop produced by coherent simplex pasting. -/
def normalizedCube (p : GenLoop (Fin 7) X x) : GenLoop (Fin 7) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationSixSimplexHomotopy x)
    (normalizationSevenSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationSixSimplexHomotopy_const x) p

theorem normalizedCube_cell (p : GenLoop (Fin 7) X x) (e : Equiv.Perm (Fin 7)) :
    (normalizedCube x p).val.comp (cubeSimplex e) =
      (normalizedSevenSimplex x (p.val.comp (cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell
    (normalizationSixSimplexHomotopy x) (normalizationSevenSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationSixSimplexHomotopy_const x) p e

/-- A genuine continuous homotopy fixing every point of the original seven-cube boundary. -/
def normalizationCubeHomotopy (p : GenLoop (Fin 7) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 7)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationSixSimplexHomotopy x)
    (normalizationSevenSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationSixSimplexHomotopy_const x) (normalizationSevenSimplexHomotopy_zero x) p

theorem normalizationCube_homotopic (p : GenLoop (Fin 7) X x) :
    GenLoop.Homotopic p (normalizedCube x p) :=
  ⟨normalizationCubeHomotopy x p⟩

theorem normalizationCube_quotient (p : GenLoop (Fin 7) X x) :
    (⟦p⟧ : π_ 7 X x) = ⟦normalizedCube x p⟧ :=
  Quotient.sound (normalizationCube_homotopic x p)

theorem normalizedCube_cell_boundary (p : GenLoop (Fin 7) X x)
    (e : Equiv.Perm (Fin 7)) (s : Simplex 7) (hs : s ∈ sevenSimplexBoundary) :
    normalizedCube x p (cubeSimplex e s) = x :=
  HigherHurewicz.coherentCubeEndpoint_cell_boundary
    (normalizationSixSimplexHomotopy x) (normalizationSevenSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationSixSimplexHomotopy_const x)
    (normalizationSixSimplexHomotopy_endpoint x) p e s hs

/-- All actual internal coordinate-equality hyperplanes of the terminal cube are based. -/
theorem normalizedCube_internalBased (p : GenLoop (Fin 7) X x)
    (u : Fin 7 → I) (i j : Fin 7) (hij : i ≠ j) (hu : u i = u j) :
    normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased
    (normalizationSixSimplexHomotopy x) (normalizationSevenSimplexHomotopy x)
    (normalizationHomotopy_face x) (normalizationSixSimplexHomotopy_const x)
    (normalizationSixSimplexHomotopy_endpoint x) p u i j hij hu

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
