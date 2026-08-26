import ErdosProblems.Erdos633b.IntegerAngleWeights

/-! A common natural angle denominator from actual bounded corner counts
and a proved nonzero integral determinant. -/

namespace Erdos633b.Tiling

theorem corner_angle_denominator_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hP : d.cornerColumnCount 0 ≤ 21) (hQ : d.cornerColumnCount 1 ≤ 5)
    (hR : d.cornerColumnCount 2 ≤ 1)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (he : (t.1 : ℝ) * d.tile.angle 0 + (t.2.1 : ℝ) * d.tile.angle 1 =
      (t.2.2 : ℝ) * Real.pi)
    (hd : cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
      (d.cornerColumnCount 2) t ≠ 0) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  let D := cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t
  let a := cornerLocalAlphaNumerator (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t
  let b := cornerLocalBetaNumerator (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t
  have hD : D ≠ 0 := hd
  have hDb : |D| ≤ 256 := corner_local_determinant_bound _ _ _ hP hQ hR t ht
  have hN : D.natAbs ≤ 256 := by
    have hh : (D.natAbs : ℤ) ≤ 256 := by simpa only [Int.natCast_natAbs] using hDb
    exact_mod_cast hh
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  obtain ⟨ha, hb⟩ := corner_local_elimination _ _ _ d.tile.angle_sum _ _ _ hc t he
  change (D : ℝ) * d.tile.angle 0 = (a : ℝ) * Real.pi at ha
  change (D : ℝ) * d.tile.angle 1 = (b : ℝ) * Real.pi at hb
  let v : Fin 3 → ℤ := ![a, b, D - a - b]
  have hv (i : Fin 3) : (D : ℝ) * d.tile.angle i = (v i : ℝ) * Real.pi := by
    fin_cases i
    · exact ha
    · exact hb
    · change (D : ℝ) * d.tile.angle 2 = ((D - a - b : ℤ) : ℝ) * Real.pi
      push_cast
      linear_combination (D : ℝ) * d.tile.angle_sum - ha - hb
  obtain ⟨hN3, w, hw, hwp, hws⟩ := d.tile.integer_angle_weights_of_scaled D hD v hv
  exact ⟨D.natAbs, hN3, hN, w, hw, hwp, hws⟩

end Erdos633b.Tiling
