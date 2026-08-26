import ErdosProblems.Erdos633b.OrderedCornerColumns
import ErdosProblems.Erdos633b.NonouterMultiplicity

/-! A repeated outer angle forces a nonouter count below the local
multiplicity. For the smallest ordered angle this gives bounded local data. -/

namespace Erdos633b.Tiling

theorem exists_count_below_multiplicity {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hP : 2 ≤ d.cornerColumnCount j)
    (k : d.NonouterVertex → ℕ)
    (hs : ∀ v, (∑ l : Fin 3, (d.vertexAngleCount v.val l : ℝ) * d.tile.angle l) =
      (k v : ℝ) * Real.pi) : ∃ v, d.vertexAngleCount v.val j < k v := by
  have hI := d.nonouter_inventory j
  have hK := d.nonouter_angle_multiplicity_sum k hs
  have he : d.cornerColumnCount j - 1 +
      (∑ v : d.NonouterVertex, d.vertexAngleCount v.val j) = ∑ v, k v := by omega
  exact exists_count_deficit (fun v : d.NonouterVertex => d.vertexAngleCount v.val j) k
    (d.cornerColumnCount j - 1) (by omega) he

theorem bounded_smallest_angle_deficit_at_vertex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3) (v : d.NonouterVertex) (k : ℕ)
    (hkpos : 1 ≤ k) (hkbound : k ≤ 2)
    (hs : (∑ j : Fin 3, (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j) =
      (k : ℝ) * Real.pi) (hv : d.vertexAngleCount v.val 0 < k) :
    ∃ p q r k : ℕ, p < k ∧ p ≤ 1 ∧ q ≤ 11 ∧ r ≤ 5 ∧ 1 ≤ k ∧ k ≤ 2 ∧
      (p : ℝ) * d.tile.angle 0 + (q : ℝ) * d.tile.angle 1 +
        (r : ℝ) * d.tile.angle 2 = (k : ℝ) * Real.pi := by
  have he := hs
  rw [Fin.sum_univ_three] at he
  have hb := d.ordered_middle_angle_gt_pi_six h01 hγ
  have hc : Real.pi / 3 < d.tile.angle 2 := by linarith [d.tile.angle_sum]
  have hk : (k : ℝ) ≤ 2 := by exact_mod_cast hkbound
  have hπ := mul_le_mul_of_nonneg_right hk Real.pi_pos.le
  have hp : 0 ≤ (d.vertexAngleCount v.val 0 : ℝ) * d.tile.angle 0 :=
    mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 0).le
  have hq : 0 ≤ (d.vertexAngleCount v.val 1 : ℝ) * d.tile.angle 1 :=
    mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 1).le
  have hr : 0 ≤ (d.vertexAngleCount v.val 2 : ℝ) * d.tile.angle 2 :=
    mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 2).le
  have hqb : d.vertexAngleCount v.val 1 ≤ 11 := by
    by_contra hn
    have hq12 : (12 : ℝ) ≤ d.vertexAngleCount v.val 1 := by
      exact_mod_cast (show 12 ≤ d.vertexAngleCount v.val 1 by omega)
    have hm := mul_le_mul_of_nonneg_right hq12 (d.tile.angle_pos 1).le
    linarith
  have hrb : d.vertexAngleCount v.val 2 ≤ 5 := by
    by_contra hn
    have hr6 : (6 : ℝ) ≤ d.vertexAngleCount v.val 2 := by
      exact_mod_cast (show 6 ≤ d.vertexAngleCount v.val 2 by omega)
    have hm := mul_le_mul_of_nonneg_right hr6 (d.tile.angle_pos 2).le
    linarith
  exact ⟨_, _, _, k, hv, by have := hkbound; omega, hqb, hrb,
    hkpos, hkbound, he⟩

theorem exists_bounded_smallest_angle_deficit {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3) (hP : 2 ≤ d.cornerColumnCount 0) :
    ∃ p q r k : ℕ, p < k ∧ p ≤ 1 ∧ q ≤ 11 ∧ r ≤ 5 ∧ 1 ≤ k ∧ k ≤ 2 ∧
      (p : ℝ) * d.tile.angle 0 + (q : ℝ) * d.tile.angle 1 +
        (r : ℝ) * d.tile.angle 2 = (k : ℝ) * Real.pi := by
  classical
  choose k hkpos hkbound hsum using d.nonouter_vertex_angle_multiple
  obtain ⟨v, hv⟩ := d.exists_count_below_multiplicity 0 hP k hsum
  exact d.bounded_smallest_angle_deficit_at_vertex h01 h12 hγ v (k v)
    (hkpos v) (hkbound v) (hsum v) hv

end Erdos633b.Tiling
