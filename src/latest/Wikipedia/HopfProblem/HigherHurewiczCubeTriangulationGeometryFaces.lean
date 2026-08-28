import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometry

/-!
# Shared faces and outer faces of the ordered cube simplices

Adjacent coordinate swaps preserve the face omitting the one changed vertex.
The first and last faces lie on the actual boundary of the native cube.
All identities retain the original simplex face parametrizations.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz

/-- An adjacent swap changes only the vertex between its two coordinate ranks. -/
theorem cubeVertex_swap_of_ne {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i : Fin n) (k : Fin (n + 2)) (hk : k ≠ i.succ.castSucc) :
    cubeVertex e k = cubeVertex ((Equiv.swap i.castSucc i.succ).trans e) k := by
  funext coord
  change (if (e.symm coord).val < k.val then (1 : I) else 0) =
    if ((Equiv.swap i.castSucc i.succ) (e.symm coord)).val < k.val then 1 else 0
  have hk' : k.val ≠ i.val + 1 := by
    intro h
    exact hk (Fin.ext h)
  by_cases h₀ : e.symm coord = i.castSucc
  · rw [h₀, Equiv.swap_apply_left]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h : i.val < k.val ↔ i.val + 1 < k.val := by omega
    simp only [h]
  by_cases h₁ : e.symm coord = i.succ
  · rw [h₁, Equiv.swap_apply_right]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h : i.val + 1 < k.val ↔ i.val < k.val := by omega
    simp only [h]
  · rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]

/-- The common interior face has literally the same affine parametrization. -/
theorem cubeSimplex_face_swap {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i : Fin n) :
    (cubeSimplex e).comp (simplexFace n i.succ.castSucc) =
      (cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e)).comp
        (simplexFace n i.succ.castSucc) := by
  simp only [cubeSimplex, cubeAffineSimplex_face]
  congr 1
  funext j
  exact cubeVertex_swap_of_ne e i _ (Fin.succAbove_ne _ _)

/-- Omitting the initial vertex fixes the first coordinate at one. -/
theorem cubeSimplex_face_zero_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex n) :
    cubeSimplex e (simplexFace n 0 s) (e 0) = 1 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (simplexFace n 0)) s (e 0) = 1
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp [cubeVertex]

/-- Omitting the final vertex fixes the last coordinate at zero. -/
theorem cubeSimplex_face_last_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex n) :
    cubeSimplex e (simplexFace n (Fin.last (n + 1)) s) (e (Fin.last n)) = 0 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp
    (simplexFace n (Fin.last (n + 1)))) s (e (Fin.last n)) = 0
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp only [cubeVertex, Equiv.symm_apply_apply, Fin.succAbove_last,
    Fin.val_castSucc, Fin.val_last]
  exact if_neg (Nat.not_lt.mpr (Nat.le_of_lt_succ j.isLt))

theorem cubeSimplex_face_zero_boundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex n) :
    cubeSimplex e (simplexFace n 0 s) ∈ Cube.boundary (Fin (n + 1)) :=
  ⟨e 0, Or.inr (cubeSimplex_face_zero_coordinate e s)⟩

theorem cubeSimplex_face_last_boundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex n) :
    cubeSimplex e (simplexFace n (Fin.last (n + 1)) s) ∈ Cube.boundary (Fin (n + 1)) :=
  ⟨e (Fin.last n), Or.inl (cubeSimplex_face_last_coordinate e s)⟩

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
