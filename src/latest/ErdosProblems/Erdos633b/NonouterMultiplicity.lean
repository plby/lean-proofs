import ErdosProblems.Erdos633b.NonouterAngleSums
import ErdosProblems.Erdos633b.AngleCountBound

/-! The total nonouter angle multiplicity is n - 1. This follows from
actual angle incidence, without a planar-graph or edge-to-edge assumption. -/

namespace Erdos633b.Tiling

theorem nonouter_angle_multiplicity_sum {T : Triangle} {n : ℕ} (d : Tiling T n)
    (k : d.NonouterVertex → ℕ)
    (hk : ∀ v, (∑ j : Fin 3, (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j) =
      (k v : ℝ) * Real.pi) : 1 + ∑ v, k v = n := by
  classical
  have hi (j : Fin 3) : (d.cornerColumnCount j : ℝ) +
      (∑ v : d.NonouterVertex, (d.vertexAngleCount v.val j : ℝ)) = n := by
    exact_mod_cast d.nonouter_inventory j
  have hs : Real.pi + (∑ v : d.NonouterVertex, (k v : ℝ)) * Real.pi =
      (n : ℝ) * Real.pi := by
    calc
      _ = (∑ j : Fin 3, (d.cornerColumnCount j : ℝ) * d.tile.angle j) +
          ∑ v : d.NonouterVertex, ∑ j : Fin 3,
            (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j := by
        rw [d.corner_column_angle_sum]
        simp_rw [hk]
        rw [Finset.sum_mul]
      _ = ∑ j : Fin 3, ((d.cornerColumnCount j : ℝ) +
          ∑ v : d.NonouterVertex, (d.vertexAngleCount v.val j : ℝ)) * d.tile.angle j := by
        rw [Finset.sum_comm]
        simp_rw [add_mul, Finset.sum_mul]
        rw [Finset.sum_add_distrib]
      _ = ∑ j : Fin 3, (n : ℝ) * d.tile.angle j := by simp_rw [hi]
      _ = (n : ℝ) * Real.pi := by
        rw [← Finset.mul_sum, Fin.sum_univ_three, d.tile.angle_sum]
  have he : (1 : ℝ) + ∑ v : d.NonouterVertex, (k v : ℝ) = n := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    linear_combination hs
  exact_mod_cast he

theorem exists_excess_corner_count {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hj : d.cornerColumnCount j = 0)
    (k : d.NonouterVertex → ℕ)
    (hk : ∀ v, (∑ l : Fin 3, (d.vertexAngleCount v.val l : ℝ) * d.tile.angle l) =
      (k v : ℝ) * Real.pi) : ∃ v, k v < d.vertexAngleCount v.val j := by
  have htotal := d.nonouter_angle_multiplicity_sum k hk
  have hi := d.nonouter_inventory j
  rw [hj, zero_add] at hi
  apply exists_count_deficit k (fun v : d.NonouterVertex => d.vertexAngleCount v.val j) 1
    (by decide)
  exact htotal.trans hi.symm

theorem angle_le_two_pi_thirds_of_missing_column {T : Triangle} {n : ℕ}
    (d : Tiling T n) (j : Fin 3) (hj : d.cornerColumnCount j = 0) :
    d.tile.angle j ≤ 2 * Real.pi / 3 := by
  classical
  choose k hkpos hkbound hsum using d.nonouter_vertex_angle_multiple
  obtain ⟨v, hv⟩ := d.exists_excess_corner_count j hj k hsum
  have hsingle : (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j ≤
      (k v : ℝ) * Real.pi := by
    rw [← hsum v]
    exact Finset.single_le_sum (fun l _ => mul_nonneg (Nat.cast_nonneg _)
      (d.tile.angle_pos l).le) (Finset.mem_univ j)
  have hle : (k v : ℝ) + 1 ≤ d.vertexAngleCount v.val j := by exact_mod_cast hv
  have hangle := mul_le_mul_of_nonneg_right hle (d.tile.angle_pos j).le
  have hk1 : k v = 1 ∨ k v = 2 := by have := hkpos v; have := hkbound v; omega
  rcases hk1 with h | h <;> rw [h] at hsingle hangle <;>
    norm_num at hsingle hangle <;> nlinarith [Real.pi_pos]

theorem corner_column_pos_of_angle_gt_two_pi_thirds {T : Triangle} {n : ℕ}
    (d : Tiling T n) (j : Fin 3) (hj : 2 * Real.pi / 3 < d.tile.angle j) :
    0 < d.cornerColumnCount j := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact (not_le_of_gt hj) (d.angle_le_two_pi_thirds_of_missing_column j hz)

end Erdos633b.Tiling
