import ErdosProblems.Erdos633b.OrderedDeficitVertex
import ErdosProblems.Erdos633b.ThreeAngleWeights

/-! The zero and unit smallest-angle corner columns are controlled by the
actual outer weights and the missing-largest-angle excess. -/

namespace Erdos633b.Tiling

theorem ordered_smallest_column_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    0 < d.cornerColumnCount 0 := by
  obtain ⟨hR, hR1⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hQ := d.ordered_middle_column_le_five h01 hγ
  have ht := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at ht
  by_contra hn
  have hP0 : d.cornerColumnCount 0 = 0 := by omega
  have hR0 : d.cornerColumnCount 2 = 0 := by
    by_contra hn
    have hh := (hR1 (by omega)).2
    omega
  have hQ5 : d.cornerColumnCount 1 = 5 := by omega
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hP0, hR0, hQ5] at hc
  norm_num at hc
  have hβ : d.tile.angle 1 = Real.pi / 5 := by linarith
  let c : Fin 3 → ℕ := fun i => d.cornerAngleCount i 1
  have hrow (i : Fin 3) : T.angle i = (c i : ℝ) * (Real.pi / 5) := by
    rw [d.angle_eq_three_counts i, d.corner_count_zero_of_column_zero 0 hP0 i,
      d.corner_count_zero_of_column_zero 2 hR0 i, hβ]
    simp only [Nat.cast_zero, zero_mul, zero_add, add_zero, c]
  have hp (i : Fin 3) : 0 < c i := by
    by_contra hn
    have hz : c i = 0 := by omega
    have hh := hrow i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (T.angle_pos i).ne' hh
  have hi : Function.Injective c := by
    intro i j hij
    apply hscalene
    rw [hrow i, hrow j, hij]
  have hs : ∑ i, c i = 5 := hQ5
  have hb := three_distinct_positive_sum_ge_six c hp hi
  omega

theorem ordered_smallest_column_one {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T)
    (hP : d.cornerColumnCount 0 = 1) :
    d.cornerColumnCount 1 = 4 ∧ d.cornerColumnCount 2 = 0 ∧
      d.tile.angle 2 = 3 * d.tile.angle 1 := by
  obtain ⟨hR, hR1⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hR0 : d.cornerColumnCount 2 = 0 := by
    by_contra hn
    have hh := (hR1 (by omega)).2
    omega
  have hQ := d.ordered_middle_column_le_five h01 hγ
  have ht := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at ht
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hP, hR0] at hc
  norm_num at hc
  have hQne : d.cornerColumnCount 1 ≠ 5 := by
    intro h5
    rw [h5] at hc
    norm_num at hc
    have hβ := d.ordered_middle_angle_gt_pi_six h01 hγ
    linarith [d.tile.angle_sum]
  have hQ4 : d.cornerColumnCount 1 = 4 := by omega
  refine ⟨hQ4, hR0, ?_⟩
  rw [hQ4] at hc
  norm_num at hc
  linarith [d.tile.angle_sum]

theorem exists_ordered_smallest_deficit {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    ∃ v : d.NonouterVertex, ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ∧ d.vertexAngleCount v.val 0 < k ∧
      (∑ j : Fin 3, (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j) =
        (k : ℝ) * Real.pi := by
  classical
  choose k hkpos hkbound hsum using d.nonouter_vertex_angle_multiple
  by_cases hP : 2 ≤ d.cornerColumnCount 0
  · obtain ⟨v, hv⟩ := d.exists_count_below_multiplicity 0 hP k hsum
    exact ⟨v, k v, hkpos v, hkbound v, hv, hsum v⟩
  · have hPpos := d.ordered_smallest_column_pos h01 h12 hγ hscalene hrep
    have hP1 : d.cornerColumnCount 0 = 1 := by omega
    obtain ⟨_, hR, hthree⟩ := d.ordered_smallest_column_one h01 h12 hγ hscalene hrep hP1
    obtain ⟨v, hv⟩ := d.exists_excess_corner_count 2 hR k hsum
    refine ⟨v, k v, hkpos v, hkbound v, ?_, hsum v⟩
    by_contra hn
    have hp : (k v : ℝ) ≤ d.vertexAngleCount v.val 0 := by
      exact_mod_cast (show k v ≤ d.vertexAngleCount v.val 0 by omega)
    have hr : (k v : ℝ) + 1 ≤ d.vertexAngleCount v.val 2 := by exact_mod_cast hv
    have hpa := mul_le_mul_of_nonneg_right hp (d.tile.angle_pos 0).le
    have hrc := mul_le_mul_of_nonneg_right hr (d.tile.angle_pos 2).le
    have hqb : 0 ≤ (d.vertexAngleCount v.val 1 : ℝ) * d.tile.angle 1 :=
      mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 1).le
    have hs := hsum v
    rw [Fin.sum_univ_three] at hs
    have hsk := congrArg (fun x : ℝ => (k v : ℝ) * x) d.tile.angle_sum
    have hcb : d.tile.angle 2 ≤ (k v : ℝ) * d.tile.angle 1 := by nlinarith
    have hk : (k v : ℝ) ≤ 2 := by exact_mod_cast hkbound v
    have hkb := mul_le_mul_of_nonneg_right hk (d.tile.angle_pos 1).le
    linarith [d.tile.angle_pos 1]

theorem exists_bounded_ordered_nonreptiling_relation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    ∃ p q r k : ℕ, p < k ∧ p ≤ 1 ∧ q ≤ 11 ∧ r ≤ 5 ∧ 1 ≤ k ∧ k ≤ 2 ∧
      (p : ℝ) * d.tile.angle 0 + (q : ℝ) * d.tile.angle 1 +
        (r : ℝ) * d.tile.angle 2 = (k : ℝ) * Real.pi := by
  obtain ⟨v, k, hkp, hkb, hv, hs⟩ := d.exists_ordered_smallest_deficit h01 h12 hγ hscalene hrep
  exact d.bounded_smallest_angle_deficit_at_vertex h01 h12 hγ v k hkp hkb hs hv

end Erdos633b.Tiling
