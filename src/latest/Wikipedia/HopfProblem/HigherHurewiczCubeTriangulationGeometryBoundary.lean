import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometryCoordinates

/-!
# The boundary and tie faces of permutation simplices

In a positive-dimensional cube, the preimage of its boundary consists of the
first and last barycentric faces. Equal adjacent ordered coordinates are the
corresponding interior barycentric face.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz

/-- Only the first and last barycentric faces map into the cube boundary. -/
theorem cubeSimplex_mem_boundary_iff {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1)) :
    cubeSimplex e s ∈ Cube.boundary (Fin (n + 1)) ↔
      s 0 = 0 ∨ s (Fin.last (n + 1)) = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    rcases hi with hi | hi
    · right
      have hlast : (cubeSimplex e s (e (Fin.last n)) : ℝ) ≤
          (cubeSimplex e s (e j) : ℝ) :=
        cubeSimplex_antitone e s (Fin.le_last j)
      have hr := congrArg (fun t : I => (t : ℝ)) hi
      change (cubeSimplex e s (e j) : ℝ) = 0 at hr
      rw [cubeSimplex_coordinate_last, hr] at hlast
      exact le_antisymm hlast (stdSimplex.zero_le s (Fin.last (n + 1)))
    · left
      have hfirst : (cubeSimplex e s (e j) : ℝ) ≤
          (cubeSimplex e s (e 0) : ℝ) :=
        cubeSimplex_antitone e s (Fin.zero_le j)
      have hr := congrArg (fun t : I => (t : ℝ)) hi
      change (cubeSimplex e s (e j) : ℝ) = 1 at hr
      rw [cubeSimplex_coordinate_zero, hr] at hfirst
      linarith [stdSimplex.zero_le s 0]
  · rintro (hs | hs)
    · refine ⟨e 0, Or.inr ?_⟩
      apply Subtype.ext
      change (cubeSimplex e s (e 0) : ℝ) = 1
      rw [cubeSimplex_coordinate_zero, hs, sub_zero]
    · refine ⟨e (Fin.last n), Or.inl ?_⟩
      apply Subtype.ext
      change (cubeSimplex e s (e (Fin.last n)) : ℝ) = 0
      rw [cubeSimplex_coordinate_last, hs]

/-- An adjacent coordinate tie lies on the corresponding interior simplex face. -/
theorem cubeSimplex_tie {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1)) (i : Fin n)
    (h : cubeSimplex e s (e i.castSucc) = cubeSimplex e s (e i.succ)) :
    s i.succ.castSucc = 0 := by
  have hd := cubeSimplex_adjacent_difference e s i
  rw [h, sub_self] at hd
  exact hd.symm

theorem cubeSimplex_tie_iff {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1)) (i : Fin n) :
    cubeSimplex e s (e i.castSucc) = cubeSimplex e s (e i.succ) ↔
      s i.succ.castSucc = 0 := by
  refine ⟨cubeSimplex_tie e s i, ?_⟩
  intro hs
  apply Subtype.ext
  have hd := cubeSimplex_adjacent_difference e s i
  rw [hs] at hd
  exact sub_eq_zero.mp hd

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
