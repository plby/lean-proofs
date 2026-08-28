import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometry
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic

/-!
# Coordinate coincidences lie on permutation-simplex boundaries

The coordinates of a cube permutation simplex are barycentric tail sums.
Equality of two distinct tails forces a barycentric coordinate between
them to vanish. This works in every dimension without enumerating
permutations or coordinate pairs.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected CubeTriangulation

/-- Equal distinct ordered tails of a simplex force an intervening coordinate to vanish. -/
theorem simplex_coordinate_zero_of_tail_eq {n : ℕ} (s : Simplex n)
    {i j : Fin n} (hij : i < j)
    (h : (∑ k : Fin (n + 1), if i.val < k.val then s k else 0) =
      ∑ k : Fin (n + 1), if j.val < k.val then s k else 0) :
    s i.succ = 0 := by
  classical
  let A := Finset.univ.filter (fun k : Fin (n + 1) => i.val < k.val)
  let B := Finset.univ.filter (fun k : Fin (n + 1) => j.val < k.val)
  have hAB : (∑ k ∈ A, s k) = ∑ k ∈ B, s k := by
    simpa only [A, B, Finset.sum_filter] using h
  have hiB : i.succ ∉ B := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, not_lt]
    exact hij
  have hsub : insert i.succ B ⊆ A := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      simp [A]
    · have hjk : j.val < k.val := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hij hjk⟩
  have hle : s i.succ + ∑ k ∈ B, s k ≤ ∑ k ∈ A, s k := by
    calc
      s i.succ + ∑ k ∈ B, s k = ∑ k ∈ insert i.succ B, s k :=
        (Finset.sum_insert hiB).symm
      _ ≤ ∑ k ∈ A, s k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => stdSimplex.zero_le s k)
  exact le_antisymm (by linarith) (stdSimplex.zero_le s i.succ)

/-- Distinct ordered coordinates can coincide only on a simplex face. -/
theorem cubeSimplex_ordered_coordinate_equality_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : cubeSimplex e s (e i) = cubeSimplex e s (e j)) :
    s ∈ simplexBoundary n := by
  have hreal := congrArg (fun t : I => (t : ℝ)) h
  rw [cubeSimplex_coordinate, cubeSimplex_coordinate] at hreal
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i.succ, simplex_coordinate_zero_of_tail_eq s hlt hreal⟩
  · exact ⟨j.succ, simplex_coordinate_zero_of_tail_eq s hgt hreal.symm⟩

/-- The same boundary conclusion for any two original native cube coordinates. -/
theorem cubeSimplex_coordinate_equality_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : cubeSimplex e s i = cubeSimplex e s j) : s ∈ simplexBoundary n := by
  apply cubeSimplex_ordered_coordinate_equality_boundary e s
    (e.symm.injective.ne hij)
  simpa only [Equiv.apply_symm_apply] using h

end Wikipedia.HopfProblem.HigherHurewicz
