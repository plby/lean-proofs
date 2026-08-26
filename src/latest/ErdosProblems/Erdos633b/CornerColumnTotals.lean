import ErdosProblems.Erdos633b.AngleRelations

/-! A nonsimilar tiling omits at least one reference angle at all outer corners. -/

namespace Erdos633b.Tiling

noncomputable def cornerColumnCount {T : Triangle} {n : ℕ} (d : Tiling T n) (j : Fin 3) : ℕ :=
  ∑ i : Fin 3, d.cornerAngleCount i j

theorem corner_column_angle_sum {T : Triangle} {n : ℕ} (d : Tiling T n) :
    (∑ j : Fin 3, (d.cornerColumnCount j : ℝ) * d.tile.angle j) = Real.pi := by
  simp only [cornerColumnCount, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← d.angle_eq_sum_counts, Fin.sum_univ_three]
  exact T.angle_sum

theorem corner_columns_one_of_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hpos : ∀ j, 0 < d.cornerColumnCount j) : ∀ j, d.cornerColumnCount j = 1 := by
  have hnonneg (j : Fin 3) : 0 ≤ ((d.cornerColumnCount j : ℝ) - 1) * d.tile.angle j := by
    apply mul_nonneg _ (d.tile.angle_pos j).le
    have hh : (1 : ℝ) ≤ d.cornerColumnCount j := by exact_mod_cast hpos j
    linarith
  have hsum : (∑ j : Fin 3, ((d.cornerColumnCount j : ℝ) - 1) * d.tile.angle j) = 0 := by
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, d.corner_column_angle_sum, Fin.sum_univ_three, d.tile.angle_sum]
    ring
  intro j
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum j (Finset.mem_univ j)
  have he : (d.cornerColumnCount j : ℝ) - 1 = 0 :=
    (mul_eq_zero.mp hz).resolve_right (d.tile.angle_pos j).ne'
  exact_mod_cast (sub_eq_zero.mp he)

theorem angles_permuted_of_corner_columns_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hpos : ∀ j, 0 < d.cornerColumnCount j) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = d.tile.angle (e i) := by
  obtain ⟨e, he⟩ := nat_matrix_permutation d.cornerAngleCount
    (d.corner_columns_one_of_pos hpos) d.corner_row_positive
  refine ⟨e, ?_⟩
  intro i
  rw [d.angle_eq_sum_counts]
  simp [he]

theorem exists_zero_corner_column_of_not_permuted {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ¬ ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = d.tile.angle (e i)) :
    ∃ j, d.cornerColumnCount j = 0 := by
  by_contra hn
  apply h
  apply d.angles_permuted_of_corner_columns_pos
  intro j
  exact Nat.pos_of_ne_zero (fun hz => hn ⟨j, hz⟩)

theorem corner_count_zero_of_column_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hj : d.cornerColumnCount j = 0) (i : Fin 3) :
    d.cornerAngleCount i j = 0 := by
  have hle := Finset.single_le_sum (f := fun i => d.cornerAngleCount i j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  change d.cornerAngleCount i j ≤ d.cornerColumnCount j at hle
  omega

theorem rational_angles_of_single_corner_column {T : Triangle} {n : ℕ} (d : Tiling T n)
    (k : Fin 3) (hz : ∀ j, j ≠ k → d.cornerColumnCount j = 0) :
    ∀ i, IsRational (T.angle i / Real.pi) := by
  have hrow (i : Fin 3) : T.angle i = (d.cornerAngleCount i k : ℝ) * d.tile.angle k := by
    rw [d.angle_eq_sum_counts]
    apply Finset.sum_eq_single k
    · intro j _ hj
      rw [d.corner_count_zero_of_column_zero j (hz j hj) i, Nat.cast_zero, zero_mul]
    · intro hk
      exact False.elim (hk (Finset.mem_univ k))
  have htotal : (d.cornerColumnCount k : ℝ) * d.tile.angle k = Real.pi := by
    have hh := d.corner_column_angle_sum
    have he : (∑ j : Fin 3, (d.cornerColumnCount j : ℝ) * d.tile.angle j) =
        (d.cornerColumnCount k : ℝ) * d.tile.angle k := by
      apply Finset.sum_eq_single k
      · intro j _ hj
        rw [hz j hj, Nat.cast_zero, zero_mul]
      · intro hk
        exact False.elim (hk (Finset.mem_univ k))
    exact he.symm.trans hh
  have hk : (d.cornerColumnCount k : ℝ) ≠ 0 := by
    intro hk
    rw [hk, zero_mul] at htotal
    exact Real.pi_ne_zero htotal.symm
  intro i
  refine ⟨(d.cornerAngleCount i k : ℚ) / d.cornerColumnCount k, ?_⟩
  push_cast
  apply (div_eq_div_iff hk Real.pi_ne_zero).mpr
  rw [hrow, ← htotal]
  ring

theorem other_corner_columns_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    0 < d.cornerColumnCount 0 ∧ 0 < d.cornerColumnCount 1 := by
  constructor
  · apply Nat.pos_of_ne_zero
    intro h0
    apply hirr
    apply d.rational_angles_of_single_corner_column 1
    intro j hj
    fin_cases j
    · exact h0
    · exact False.elim (hj rfl)
    · exact h2
  · apply Nat.pos_of_ne_zero
    intro h1
    apply hirr
    apply d.rational_angles_of_single_corner_column 0
    intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact h1
    · exact h2

end Erdos633b.Tiling
