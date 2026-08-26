import ErdosProblems.Erdos633b.OrderedDeficitVertex

/-! A middle angle above two fifths of pi forces tight two-angle counts
at every actual nonouter vertex. -/

namespace Erdos633b

theorem large_middle_local_bound (α β γ : ℝ) (hα : 0 < α) (hβγ : β < γ)
    (hβ : 2 * Real.pi / 5 < β) (p q r k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (he : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = (k : ℝ) * Real.pi) :
    q + r ≤ 2 * k := by
  have hbpos : 0 < β := by linarith [Real.pi_pos]
  have hpa := mul_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) hα.le
  have hrc := mul_le_mul_of_nonneg_left hβγ.le (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hqr : ((q : ℝ) + r) * β ≤ (k : ℝ) * Real.pi := by nlinarith
  by_contra hn
  have hh : ((2 * k + 1 : ℕ) : ℝ) ≤ (q : ℝ) + r := by
    exact_mod_cast (show 2 * k + 1 ≤ q + r by omega)
  have hm := mul_le_mul_of_nonneg_right hh hbpos.le
  have hk : k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl <;> norm_num at hm hqr <;> linarith

theorem deficit_column_three (P p r k : ℕ) (hP : 3 ≤ P) (hp : p < k)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 2) (hr : r ≤ 2 * k)
    (he : p + P * r = r + P * k) : P = 3 := by
  have hp1 : p ≤ 1 := by omega
  have hr4 : r ≤ 4 := by omega
  interval_cases k <;> interval_cases p <;> interval_cases r <;> omega

namespace Tiling

theorem large_middle_corner_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hβ : 2 * Real.pi / 5 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    3 ≤ d.cornerColumnCount 0 ∧ d.cornerColumnCount 1 = 2 ∧ d.cornerColumnCount 2 = 0 := by
  classical
  choose k hk1 hk2 he using d.nonouter_vertex_angle_multiple
  have hlocal (v : d.NonouterVertex) : d.vertexAngleCount v.val 1 +
      d.vertexAngleCount v.val 2 ≤ 2 * k v := by
    apply large_middle_local_bound _ _ _ (d.tile.angle_pos 0) h12 hβ _ _ _ _ (hk1 v) (hk2 v)
    simpa only [Fin.sum_univ_three] using he v
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hlocal v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hi1 := d.nonouter_inventory 1
  have hi2 := d.nonouter_inventory 2
  have hk := d.nonouter_angle_multiplicity_sum k he
  have hQR : 2 ≤ d.cornerColumnCount 1 + d.cornerColumnCount 2 := by omega
  obtain ⟨hRle, hRone⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hR : d.cornerColumnCount 2 = 0 := by
    by_contra hn
    have hh := (hRone (by omega)).1
    omega
  have hQle : d.cornerColumnCount 1 ≤ 2 := by
    have hc := d.corner_column_angle_sum
    rw [Fin.sum_univ_three, hR, Nat.cast_zero, zero_mul, add_zero] at hc
    have hp := mul_nonneg (Nat.cast_nonneg (d.cornerColumnCount 0) : (0 : ℝ) ≤ _)
      (d.tile.angle_pos 0).le
    by_contra hn
    have hQ3 : (3 : ℝ) ≤ d.cornerColumnCount 1 := by
      exact_mod_cast (show 3 ≤ d.cornerColumnCount 1 by omega)
    have hm := mul_le_mul_of_nonneg_right hQ3 (d.tile.angle_pos 1).le
    linarith [Real.pi_pos]
  have hQ : d.cornerColumnCount 1 = 2 := by omega
  have ht := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at ht
  exact ⟨by omega, hQ, hR⟩

theorem large_middle_local_equality {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h12 : d.tile.angle 1 < d.tile.angle 2) (hβ : 2 * Real.pi / 5 < d.tile.angle 1)
    (hQ : d.cornerColumnCount 1 = 2) (hR : d.cornerColumnCount 2 = 0)
    (k : d.NonouterVertex → ℕ) (hk1 : ∀ v, 1 ≤ k v) (hk2 : ∀ v, k v ≤ 2)
    (he : ∀ v, (∑ j : Fin 3, (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j) =
      (k v : ℝ) * Real.pi) (v : d.NonouterVertex) :
    d.vertexAngleCount v.val 1 + d.vertexAngleCount v.val 2 = 2 * k v := by
  classical
  have hlocal (w : d.NonouterVertex) : d.vertexAngleCount w.val 1 +
      d.vertexAngleCount w.val 2 ≤ 2 * k w := by
    apply large_middle_local_bound _ _ _ (d.tile.angle_pos 0) h12 hβ _ _ _ _ (hk1 w) (hk2 w)
    simpa only [Fin.sum_univ_three] using he w
  have hi1 := d.nonouter_inventory 1
  have hi2 := d.nonouter_inventory 2
  have hk := d.nonouter_angle_multiplicity_sum k he
  have hsum : (∑ w : d.NonouterVertex,
      (d.vertexAngleCount w.val 1 + d.vertexAngleCount w.val 2)) = ∑ w, 2 * k w := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    omega
  by_contra hn
  have hlt := Finset.sum_lt_sum (fun w (_ : w ∈ Finset.univ) => hlocal w)
    ⟨v, Finset.mem_univ v, lt_of_le_of_ne (hlocal v) hn⟩
  omega

theorem large_middle_groupOne_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hβ : 2 * Real.pi / 5 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    d.cornerColumnCount 0 = 3 ∧ d.cornerColumnCount 1 = 2 ∧ d.cornerColumnCount 2 = 0 := by
  classical
  obtain ⟨hP, hQ, hR⟩ := d.large_middle_corner_columns h01 h12 hβ hscalene hrep
  choose k hk1 hk2 he using d.nonouter_vertex_angle_multiple
  obtain ⟨v, hv⟩ := d.exists_count_below_multiplicity 0 (by omega) k he
  have hqr := d.large_middle_local_equality h12 hβ hQ hR k hk1 hk2 he v
  have hqrr : (d.vertexAngleCount v.val 1 : ℝ) + d.vertexAngleCount v.val 2 = 2 * k v := by
    exact_mod_cast hqr
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hQ, hR] at hc
  norm_num only [Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero] at hc
  have hlocal := he v
  rw [Fin.sum_univ_three] at hlocal
  have hnum : (d.vertexAngleCount v.val 0 : ℝ) +
      d.cornerColumnCount 0 * d.vertexAngleCount v.val 2 =
      d.vertexAngleCount v.val 2 + d.cornerColumnCount 0 * k v := by
    apply mul_right_cancel₀ (d.tile.angle_pos 0).ne'
    linear_combination hlocal - (d.vertexAngleCount v.val 2 : ℝ) * d.tile.angle_sum -
      ((k v : ℝ) - d.vertexAngleCount v.val 2) * hc - d.tile.angle 1 * hqrr
  have hnum' : d.vertexAngleCount v.val 0 +
      d.cornerColumnCount 0 * d.vertexAngleCount v.val 2 =
      d.vertexAngleCount v.val 2 + d.cornerColumnCount 0 * k v := by exact_mod_cast hnum
  exact ⟨deficit_column_three _ _ _ _ hP hv (hk1 v) (hk2 v) (by omega) hnum', hQ, hR⟩

end Tiling
end Erdos633b
