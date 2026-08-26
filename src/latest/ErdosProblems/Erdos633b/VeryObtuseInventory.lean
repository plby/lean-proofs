import ErdosProblems.Erdos633b.NonouterMultiplicity

/-! An angle greater than 120 degrees occurs once at the outer corners,
and its nonouter counts equal the local angle multiplicities. -/

namespace Erdos633b.Tiling

theorem corner_column_one_of_very_obtuse {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hlarge : 2 * Real.pi / 3 < d.tile.angle j) :
    d.cornerColumnCount j = 1 := by
  have hp := d.corner_column_pos_of_angle_gt_two_pi_thirds j hlarge
  have hle : (d.cornerColumnCount j : ℝ) * d.tile.angle j ≤ Real.pi := by
    rw [← d.corner_column_angle_sum]
    exact Finset.single_le_sum (fun l _ => mul_nonneg (Nat.cast_nonneg _)
      (d.tile.angle_pos l).le) (Finset.mem_univ j)
  have hb : d.cornerColumnCount j ≤ 1 := by
    by_contra h
    have hh : (2 : ℝ) ≤ d.cornerColumnCount j := by
      exact_mod_cast (show 2 ≤ d.cornerColumnCount j by omega)
    have hm := mul_le_mul_of_nonneg_right hh (d.tile.angle_pos j).le
    linarith [Real.pi_pos]
  omega

theorem vertex_count_eq_multiplicity_of_very_obtuse {T : Triangle} {n : ℕ}
    (d : Tiling T n) (j : Fin 3) (hlarge : 2 * Real.pi / 3 < d.tile.angle j)
    (k : d.NonouterVertex → ℕ) (hkpos : ∀ v, 1 ≤ k v) (hkbound : ∀ v, k v ≤ 2)
    (hsum : ∀ v, (∑ l : Fin 3, (d.vertexAngleCount v.val l : ℝ) * d.tile.angle l) =
      (k v : ℝ) * Real.pi) : ∀ v, d.vertexAngleCount v.val j = k v := by
  classical
  have hle (v : d.NonouterVertex) : d.vertexAngleCount v.val j ≤ k v := by
    by_contra h
    have hc : (k v : ℝ) + 1 ≤ d.vertexAngleCount v.val j := by
      exact_mod_cast (show k v < d.vertexAngleCount v.val j by omega)
    have hm := mul_le_mul_of_nonneg_right hc (d.tile.angle_pos j).le
    have hs : (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j ≤ (k v : ℝ) * Real.pi := by
      rw [← hsum v]
      exact Finset.single_le_sum (fun l _ => mul_nonneg (Nat.cast_nonneg _)
        (d.tile.angle_pos l).le) (Finset.mem_univ j)
    have hk : k v = 1 ∨ k v = 2 := by have := hkpos v; have := hkbound v; omega
    rcases hk with hk | hk <;> rw [hk] at hm hs <;> norm_num at hm hs <;> linarith [Real.pi_pos]
  have hi := d.nonouter_inventory j
  rw [d.corner_column_one_of_very_obtuse j hlarge] at hi
  have ht := d.nonouter_angle_multiplicity_sum k hsum
  have he : ∑ v : d.NonouterVertex, d.vertexAngleCount v.val j = ∑ v, k v := by omega
  intro v
  exact (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp he v (Finset.mem_univ v)

theorem other_column_le_three_of_very_obtuse {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hlarge : 2 * Real.pi / 3 < d.tile.angle 2) (h1 : d.cornerColumnCount 1 = 0) :
    d.cornerColumnCount 0 ≤ 3 := by
  classical
  by_contra hn
  have hP : (4 : ℝ) ≤ d.cornerColumnCount 0 := by
    exact_mod_cast (show 4 ≤ d.cornerColumnCount 0 by omega)
  have h2 := d.corner_column_one_of_very_obtuse 2 hlarge
  have hcorner := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, h1, h2] at hcorner
  simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero] at hcorner
  have hbeta : 2 * d.tile.angle 0 < d.tile.angle 1 := by
    have hm := mul_le_mul_of_nonneg_right hP (d.tile.angle_pos 0).le
    linarith [d.tile.angle_sum, d.tile.angle_pos 0]
  choose k hkpos hkbound hsum using d.nonouter_vertex_angle_multiple
  have hr := d.vertex_count_eq_multiplicity_of_very_obtuse 2 hlarge k hkpos hkbound hsum
  have hq (v : d.NonouterVertex) : d.vertexAngleCount v.val 1 ≤ k v := by
    by_contra hh
    have hc : (k v : ℝ) + 1 ≤ d.vertexAngleCount v.val 1 := by
      exact_mod_cast (show k v < d.vertexAngleCount v.val 1 by omega)
    have hs := hsum v
    rw [Fin.sum_univ_three, hr v] at hs
    have he : (d.vertexAngleCount v.val 0 : ℝ) * d.tile.angle 0 +
        (d.vertexAngleCount v.val 1 : ℝ) * d.tile.angle 1 =
          (k v : ℝ) * (d.tile.angle 0 + d.tile.angle 1) := by
      linear_combination hs - (k v : ℝ) * d.tile.angle_sum
    have hm := mul_le_mul_of_nonneg_right hc (d.tile.angle_pos 1).le
    have hk : (k v : ℝ) ≤ 2 := by exact_mod_cast hkbound v
    have hka := mul_le_mul_of_nonneg_right hk (d.tile.angle_pos 0).le
    have hp : 0 ≤ (d.vertexAngleCount v.val 0 : ℝ) * d.tile.angle 0 :=
      mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 0).le
    nlinarith
  have hi := d.nonouter_inventory 1
  rw [h1, zero_add] at hi
  have ht := d.nonouter_angle_multiplicity_sum k hsum
  have hqsum : ∑ v : d.NonouterVertex, d.vertexAngleCount v.val 1 ≤ ∑ v, k v :=
    Finset.sum_le_sum (fun v _ => hq v)
  omega

end Erdos633b.Tiling
