import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometry

/-!
# Recovering barycentric coordinates from ordered cube coordinates

The first and last coefficients are the two endpoint gaps, and every interior
coefficient is a difference of adjacent ordered cube coordinates.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz

theorem cubeSimplex_coordinate_zero {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1)) :
    (cubeSimplex e s (e 0) : ℝ) = 1 - s 0 := by
  rw [cubeSimplex_coordinate, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.lt_irrefl, if_false, Fin.val_succ,
    Nat.zero_lt_succ, if_true, zero_add]
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  linarith

theorem cubeSimplex_coordinate_last {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1)) :
    (cubeSimplex e s (e (Fin.last n)) : ℝ) = s (Fin.last (n + 1)) := by
  rw [cubeSimplex_coordinate, Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc, Nat.lt_succ_self, if_true]
  have hz : (∑ k : Fin (n + 1), if n < k.val then s k.castSucc else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (Nat.not_lt.mpr (Nat.le_of_lt_succ k.isLt))
  rw [hz, zero_add]

/-- The gap between neighboring ordered coordinates is their common-face coefficient. -/
theorem cubeSimplex_adjacent_difference {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1)) (i : Fin n) :
    (cubeSimplex e s (e i.castSucc) : ℝ) -
        (cubeSimplex e s (e i.succ) : ℝ) = s i.succ.castSucc := by
  rw [cubeSimplex_coordinate, cubeSimplex_coordinate, ← Finset.sum_sub_distrib]
  calc
    ∑ k : Fin (n + 2),
        ((if i.castSucc.val < k.val then s k else 0) -
          (if i.succ.val < k.val then s k else 0)) =
        ∑ k : Fin (n + 2), if k = i.succ.castSucc then s k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i.succ.castSucc
      · subst k
        simp
      · have hv : k.val ≠ i.val + 1 := by
          intro h
          apply hk
          exact Fin.ext h
        by_cases h : i.val < k.val
        · have h' : i.val + 1 < k.val := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, if_pos h, if_pos h',
            if_neg hk, sub_self]
        · have h' : ¬ i.val + 1 < k.val := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, if_neg h, if_neg h',
            if_neg hk, sub_zero]
    _ = s i.succ.castSucc := by simp

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
