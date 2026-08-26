import ErdosProblems.Erdos633b.RationalCornerRows
import ErdosProblems.Erdos633b.CornerReindex

/-! Commensurability of the tile and of a nonequilateral outer triangle
is equivalent. This follows from the actual vertex inventory, including
the case where only one reference angle occurs at the outer corners. -/

namespace Erdos633b.Tiling

theorem corner_column_three_of_positive_rows {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hb : d.cornerColumnCount j ≤ 3) (hp : ∀ i, 0 < d.cornerAngleCount i j) :
    d.cornerColumnCount j = 3 ∧ ∀ i, d.cornerAngleCount i j = 1 := by
  have hs : d.cornerColumnCount j = d.cornerAngleCount 0 j + d.cornerAngleCount 1 j +
      d.cornerAngleCount 2 j := by simp only [cornerColumnCount, Fin.sum_univ_three]
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  refine ⟨by omega, ?_⟩
  intro i
  fin_cases i
  · change d.cornerAngleCount 0 j = 1
    omega
  · change d.cornerAngleCount 1 j = 1
    omega
  · change d.cornerAngleCount 2 j = 1
    omega

theorem equilateral_of_rational_outer_missing_column {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hrat : ∀ i, IsRational (T.angle i / Real.pi)) : ∀ i, T.angle i = Real.pi / 3 := by
  obtain ⟨hP, hQ⟩ := d.corner_columns_le_three_of_tile h2 hirr
  have hex : ∃ j : Fin 3, j ≠ 2 ∧ 0 < d.cornerColumnCount j ∧ d.cornerColumnCount j ≤ 3 := by
    by_cases hp : 0 < d.cornerColumnCount 0
    · exact ⟨0, by decide, hp, hP⟩
    · have hq : 0 < d.cornerColumnCount 1 := by
        by_contra hn
        have hp0 : d.cornerColumnCount 0 = 0 := by omega
        have hq0 : d.cornerColumnCount 1 = 0 := by omega
        have hs := d.corner_two_angle_sum h2
        simp only [hp0, hq0, Nat.cast_zero, zero_mul, zero_add] at hs
        exact Real.pi_ne_zero hs.symm
      exact ⟨1, by decide, hq, hQ⟩
  obtain ⟨j, hj, hp, hb⟩ := hex
  obtain ⟨hc, hrows⟩ := d.corner_column_three_of_positive_rows j hb
    (d.rational_corner_row_positive h2 hirr hrat j hj hp)
  intro i
  obtain ⟨t, ht⟩ := hrat i
  obtain ⟨he0, he1⟩ := d.rational_corner_row_proportional h2 hirr i t ht
  have he : (d.cornerAngleCount i j : ℝ) = (t : ℝ) * d.cornerColumnCount j := by
    fin_cases j
    · exact he0
    · exact he1
    · exact False.elim (hj rfl)
  rw [hrows i, hc] at he
  norm_num at he
  have htval : (t : ℝ) = 1 / 3 := by linarith
  have ht' := (eq_div_iff Real.pi_ne_zero).mp ht
  rw [htval] at ht'
  linarith

theorem equilateral_of_rational_outer_incommensurable_tile {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hrat : ∀ i, IsRational (T.angle i / Real.pi))
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi)) : ∀ i, T.angle i = Real.pi / 3 := by
  have hrep : ¬ ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = d.tile.angle (e i) := by
    rintro ⟨e, he⟩
    apply hirr
    intro i
    have h := hrat (e.symm i)
    rw [he (e.symm i), Equiv.apply_symm_apply] at h
    exact h
  obtain ⟨e, he⟩ := d.exists_reindex_zero_last_corner_column hrep
  let d' := d.reindexTile e
  have hirr' : ¬ ∀ i, IsRational (d'.tile.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    have hh := h (e i)
    change IsRational (Triangle.angle (d.tile.reindex e) (e i) / Real.pi) at hh
    simpa only [Triangle.angle_reindex, Equiv.symm_apply_apply] using hh
  exact d'.equilateral_of_rational_outer_missing_column he hirr' hrat

theorem rational_tile_angles_of_outer {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hne : ¬ ∀ i, T.angle i = Real.pi / 3) (hrat : ∀ i, IsRational (T.angle i / Real.pi)) :
    ∀ i, IsRational (d.tile.angle i / Real.pi) := by
  by_contra hirr
  exact hne (d.equilateral_of_rational_outer_incommensurable_tile hrat hirr)

theorem tile_angles_rational_iff_outer {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hne : ¬ ∀ i, T.angle i = Real.pi / 3) :
    (∀ i, IsRational (d.tile.angle i / Real.pi)) ↔ ∀ i, IsRational (T.angle i / Real.pi) :=
  ⟨d.rational_angles_of_tile, d.rational_tile_angles_of_outer hne⟩

theorem outer_incommensurable_of_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hne : ¬ ∀ i, T.angle i = Real.pi / 3)
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi)) :
    ¬ ∀ i, IsRational (T.angle i / Real.pi) := by
  intro hrat
  exact hirr (d.rational_tile_angles_of_outer hne hrat)

end Erdos633b.Tiling
