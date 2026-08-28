import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCoverCoordinates
import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCoverSortTies

/-!
# Exact barycentric agreement on tetrahedral overlaps

Different sorting permutations give the same ordered coordinate values,
so their successive differences are the same barycentric point. This
handles every overlap, including edges where all three coordinates tie.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation

open FirstHurewicz Geometry

theorem cubeBarycentric_eq_of_sorted (u : Cube3) {e f : Equiv.Perm (Fin 3)}
    (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    cubeBarycentric e u = cubeBarycentric f u := by
  simp only [cubeBarycentric, sorted_values_eq u he hf 0,
    sorted_values_eq u he hf 1, sorted_values_eq u he hf 2]

theorem cubeTetrahedronInverse_sorted_eq (u : Cube3) {e f : Equiv.Perm (Fin 3)}
    (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    cubeTetrahedronInverse e ⟨u, he⟩ = cubeTetrahedronInverse f ⟨u, hf⟩ :=
  Subtype.ext (cubeBarycentric_eq_of_sorted u he hf)

/-- The same barycentric point represents the cube point in every order region containing it. -/
theorem cubeTetrahedron_eq_of_sorted (e f : Equiv.Perm (Fin 3)) (s : Simplex 3)
    (hf : SortedCoordinates (cubeTetrahedron e s) f) :
    cubeTetrahedron f s = cubeTetrahedron e s := by
  have hp : cubeTetrahedronInverse f ⟨cubeTetrahedron e s, hf⟩ = s :=
    (cubeTetrahedronInverse_sorted_eq (cubeTetrahedron e s)
      hf (cubeTetrahedron_sorted e s)).trans (cubeTetrahedronInverse_tetrahedron e s)
  simpa only [hp] using cubeTetrahedron_inverse f ⟨cubeTetrahedron e s, hf⟩

/-- Equal cube images in any two cells have identical barycentric preimages. -/
theorem cubeTetrahedron_overlap_preimage (e f : Equiv.Perm (Fin 3))
    (s t : Simplex 3) (h : cubeTetrahedron e s = cubeTetrahedron f t) : s = t := by
  have hf : SortedCoordinates (cubeTetrahedron e s) f := by
    rw [h]
    exact cubeTetrahedron_sorted f t
  exact cubeTetrahedron_injective f ((cubeTetrahedron_eq_of_sorted e f s hf).trans h)

end Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation
