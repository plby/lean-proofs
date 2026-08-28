import Wikipedia.HopfProblem.ThirdHurewiczCubeGluingCells
import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCoverOverlaps

/-!
# Coherent face homotopies agree on every tetrahedral overlap

Equal cube images have the same barycentric point. All permutations
containing that image are linked by adjacent swaps of tied coordinates.
Each such swap is one of the actual common simplex faces, where the
given coherent homotopies agree. This proves the geometric pasting condition.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing

open FirstHurewicz Geometry CubeTriangulation SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X}

theorem coherentCubeFamily_compatible
    (H₂ : C(Simplex 2, X) → C(I × Simplex 2, X))
    (H₃ : C(Simplex 3, X) → C(I × Simplex 3, X))
    (hface : FaceCompatibleHomotopies 2 H₂ H₃) (p : GenLoop (Fin 3) X x) :
    CubeCompatible (fun e => H₃ (p.val.comp (cubeTetrahedron e))) := by
  intro e f s t h r
  have hst := cubeTetrahedron_overlap_preimage e f s t h
  subst t
  have hf : SortedCoordinates (cubeTetrahedron e s) f := by
    rw [h]
    exact cubeTetrahedron_sorted f s
  apply eq_of_sorted_adjacent (cubeTetrahedron e s)
    (fun g => H₃ (p.val.comp (cubeTetrahedron g)) (r, s))
    ?_ ?_ (cubeTetrahedron_sorted e s) hf
  · intro g hg ht
    apply coherentCubeCell_one_swap H₂ H₃ hface p g r s
    apply cubeTetrahedron_tie_first g s
    simpa only [cubeTetrahedron_eq_of_sorted e g s hg] using ht
  · intro g hg ht
    apply coherentCubeCell_two_swap H₂ H₃ hface p g r s
    apply cubeTetrahedron_tie_second g s
    simpa only [cubeTetrahedron_eq_of_sorted e g s hg] using ht

end Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing
