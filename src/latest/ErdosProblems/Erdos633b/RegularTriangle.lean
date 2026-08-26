import ErdosProblems.Erdos633b.RationalAngleSides
import ErdosProblems.Erdos633b.NonouterMultiplicity

/-! Equal counts of two reference angles at every actual tiling vertex
force an equilateral outer triangle, directly from the geometric inventory. -/

namespace Erdos633b

namespace Triangle

theorem equilateral_of_angle_multiples (T : Triangle) (x : ℝ) (hx : Real.pi / 3 ≤ x)
    (c : Fin 3 → ℕ) (hrow : ∀ i, T.angle i = (c i : ℝ) * x) :
    ∀ i, T.angle i = Real.pi / 3 := by
  apply T.equilateral_of_angles_ge_pi_third
  intro i
  have hc : 0 < c i := by
    by_contra hn
    have hz : c i = 0 := by omega
    have hh := hrow i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (T.angle_pos i).ne' hh
  have hc' : (1 : ℝ) ≤ c i := by exact_mod_cast hc
  rw [hrow]
  have hh := mul_le_mul_of_nonneg_right hc' (show 0 ≤ x by linarith [Real.pi_pos])
  linarith

end Triangle
namespace Tiling

theorem equilateral_of_equal_first_two_vertex_counts {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ v : d.Vertex, d.vertexAngleCount v 0 = d.vertexAngleCount v 1) :
    ∀ i, T.angle i = Real.pi / 3 := by
  classical
  have hc (i : Fin 3) : d.cornerAngleCount i 0 = d.cornerAngleCount i 1 := by
    simpa only [d.vertexAngleCount_outer] using h (d.outerVertex i)
  have hPQ : d.cornerColumnCount 0 = d.cornerColumnCount 1 := by
    simp only [cornerColumnCount, hc]
  have hrowpos (i : Fin 3) : 1 ≤ d.cornerAngleCount i 0 + d.cornerAngleCount i 2 := by
    obtain ⟨j, hj⟩ := d.corner_row_positive i
    have he := hc i
    fin_cases j
    · change 0 < d.cornerAngleCount i 0 at hj
      omega
    · change 0 < d.cornerAngleCount i 1 at hj
      omega
    · change 0 < d.cornerAngleCount i 2 at hj
      omega
  have hPR : 3 ≤ d.cornerColumnCount 0 + d.cornerColumnCount 2 := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hrowpos i)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, cornerColumnCount] using hs
  have hzero : d.cornerColumnCount 0 = 0 ∨ d.cornerColumnCount 2 = 0 := by
    by_contra hn
    have h0 : 0 < d.cornerColumnCount 0 := by omega
    have h2 : 0 < d.cornerColumnCount 2 := by omega
    have hpos (j : Fin 3) : 0 < d.cornerColumnCount j := by
      fin_cases j
      · exact h0
      · exact hPQ ▸ h0
      · exact h2
    have hall := d.corner_columns_one_of_pos hpos
    have hP := hall 0
    have hR := hall 2
    omega
  rcases hzero with hP | hR
  · have hγ : Real.pi / 3 ≤ d.tile.angle 2 := by
      by_contra hn
      have hx : 2 * Real.pi / 3 < d.tile.angle 0 + d.tile.angle 1 := by
        linarith [d.tile.angle_sum]
      choose k hkpos hkbound hsum using d.nonouter_vertex_angle_multiple
      obtain ⟨v, hv⟩ := d.exists_excess_corner_count 0 hP k hsum
      have he := hsum v
      rw [Fin.sum_univ_three, ← h v.val, ← mul_add] at he
      have hr : 0 ≤ (d.vertexAngleCount v.val 2 : ℝ) * d.tile.angle 2 :=
        mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 2).le
      have hv' : (k v : ℝ) + 1 ≤ d.vertexAngleCount v.val 0 := by exact_mod_cast hv
      have hm := mul_le_mul_of_nonneg_right hv'
        (show 0 ≤ d.tile.angle 0 + d.tile.angle 1 by linarith [Real.pi_pos])
      have hkv : k v = 1 ∨ k v = 2 := by
        have hp := hkpos v
        have hb := hkbound v
        omega
      rcases hkv with hkv | hkv <;> rw [hkv] at he hm <;>
        norm_num at he hm <;> linarith [Real.pi_pos]
    apply T.equilateral_of_angle_multiples (d.tile.angle 2) hγ
      (fun i => d.cornerAngleCount i 2)
    intro i
    have h0 := d.corner_count_zero_of_column_zero 0 hP i
    have h1 : d.cornerAngleCount i 1 = 0 := (hc i).symm.trans h0
    rw [d.angle_eq_three_counts i, h0, h1]
    simp only [Nat.cast_zero, zero_mul, zero_add]
  · have hγ := d.angle_le_two_pi_thirds_of_missing_column 2 hR
    have hx : Real.pi / 3 ≤ d.tile.angle 0 + d.tile.angle 1 := by
      linarith [d.tile.angle_sum]
    apply T.equilateral_of_angle_multiples (d.tile.angle 0 + d.tile.angle 1) hx
      (fun i => d.cornerAngleCount i 0)
    intro i
    rw [d.angle_eq_three_counts i, ← hc i, d.corner_count_zero_of_column_zero 2 hR i]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    ring

end Tiling
end Erdos633b
