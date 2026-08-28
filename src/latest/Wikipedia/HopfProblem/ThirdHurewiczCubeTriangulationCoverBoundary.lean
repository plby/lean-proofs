import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometry
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# The boundary and tie faces of the actual cube tetrahedra

Only the first and last barycentric faces lie in the cube boundary.
The two interior barycentric faces correspond exactly to adjacent equal
ordered cube coordinates.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation

open Geometry FirstHurewicz SecondHurewicz.SimplyConnected

/-- The precise preimage of the cube boundary under a permutation tetrahedron. -/
theorem cubeTetrahedron_mem_boundary_iff (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    cubeTetrahedron e s ∈ Cube.boundary (Fin 3) ↔ s 0 = 0 ∨ s 3 = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    have h0 := stdSimplex.zero_le s 0
    have h1 := stdSimplex.zero_le s 1
    have h2 := stdSimplex.zero_le s 2
    have h3 := stdSimplex.zero_le s 3
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
    fin_cases j
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : I => (t : ℝ)) hi
        change (cubeTetrahedron e s (e 0) : ℝ) = 0 at hr
        rw [cubeTetrahedron_coordinate_zero] at hr
        linarith
      · left
        have hr := congrArg (fun t : I => (t : ℝ)) hi
        change (cubeTetrahedron e s (e 0) : ℝ) = 1 at hr
        rw [cubeTetrahedron_coordinate_zero] at hr
        linarith
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : I => (t : ℝ)) hi
        change (cubeTetrahedron e s (e 1) : ℝ) = 0 at hr
        rw [cubeTetrahedron_coordinate_one] at hr
        linarith
      · left
        have hr := congrArg (fun t : I => (t : ℝ)) hi
        change (cubeTetrahedron e s (e 1) : ℝ) = 1 at hr
        rw [cubeTetrahedron_coordinate_one] at hr
        linarith
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : I => (t : ℝ)) hi
        change (cubeTetrahedron e s (e 2) : ℝ) = 0 at hr
        rwa [cubeTetrahedron_coordinate_two] at hr
      · left
        have hr := congrArg (fun t : I => (t : ℝ)) hi
        change (cubeTetrahedron e s (e 2) : ℝ) = 1 at hr
        rw [cubeTetrahedron_coordinate_two] at hr
        linarith
  · rintro (hs | hs)
    · have ht := cubeTetrahedron_face_zero_boundary e (simplexFaceInverse 2 0 ⟨s, hs⟩)
      simpa only [simplexFace_inverse] using ht
    · have ht := cubeTetrahedron_face_three_boundary e (simplexFaceInverse 2 3 ⟨s, hs⟩)
      simpa only [simplexFace_inverse] using ht

/-- A tie of the first two ordered cube coordinates is the first interior face. -/
theorem cubeTetrahedron_tie_first (e : Equiv.Perm (Fin 3)) (s : Simplex 3)
    (h : cubeTetrahedron e s (e 0) = cubeTetrahedron e s (e 1)) : s 1 = 0 := by
  have hr := congrArg (fun t : I => (t : ℝ)) h
  rw [cubeTetrahedron_coordinate_zero, cubeTetrahedron_coordinate_one] at hr
  linarith

/-- A tie of the last two ordered cube coordinates is the second interior face. -/
theorem cubeTetrahedron_tie_second (e : Equiv.Perm (Fin 3)) (s : Simplex 3)
    (h : cubeTetrahedron e s (e 1) = cubeTetrahedron e s (e 2)) : s 2 = 0 := by
  have hr := congrArg (fun t : I => (t : ℝ)) h
  rw [cubeTetrahedron_coordinate_one, cubeTetrahedron_coordinate_two] at hr
  linarith

end Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation
