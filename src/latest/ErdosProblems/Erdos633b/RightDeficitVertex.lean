import ErdosProblems.Erdos633b.RightCornerAlternatives
import ErdosProblems.Erdos633b.NonouterMultiplicity

/-! An actual nonouter vertex with excess beta corners supplies uniformly
bounded counts for the right-tile arithmetic reduction. -/

namespace Erdos633b.Tiling

theorem exists_right_beta_excess {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hαβ : d.tile.angle 0 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    ∃ p q r k : ℕ, p < q ∧ q ≤ 7 ∧ r ≤ 3 ∧ 1 ≤ k ∧ k ≤ 2 ∧
      (p : ℝ) * d.tile.angle 0 + (q : ℝ) * d.tile.angle 1 +
        (r : ℝ) * (Real.pi / 2) = (k : ℝ) * Real.pi := by
  classical
  obtain ⟨hP, hQR⟩ := d.right_corner_column_alternatives hright hαβ hscalene hrep
  have hPQ : d.cornerColumnCount 1 < d.cornerColumnCount 0 := by omega
  have hi0 := d.nonouter_inventory 0
  have hi1 := d.nonouter_inventory 1
  have hb : d.cornerColumnCount 0 - d.cornerColumnCount 1 +
      (∑ v : d.NonouterVertex, d.vertexAngleCount v.val 0) =
      ∑ v : d.NonouterVertex, d.vertexAngleCount v.val 1 := by omega
  obtain ⟨v, hv⟩ := exists_count_deficit
    (fun v : d.NonouterVertex => d.vertexAngleCount v.val 0)
    (fun v : d.NonouterVertex => d.vertexAngleCount v.val 1)
    (d.cornerColumnCount 0 - d.cornerColumnCount 1) (Nat.sub_pos_of_lt hPQ) hb
  obtain ⟨k, hkp, hkb, hs⟩ := d.nonouter_vertex_angle_multiple v
  rw [Fin.sum_univ_three, hright] at hs
  have hβ4 : Real.pi / 4 < d.tile.angle 1 := by linarith [d.tile.angle_sum]
  have hk : (k : ℝ) ≤ 2 := by exact_mod_cast hkb
  have hkpireal := mul_le_mul_of_nonneg_right hk Real.pi_pos.le
  have hp : 0 ≤ (d.vertexAngleCount v.val 0 : ℝ) * d.tile.angle 0 :=
    mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 0).le
  have hr : 0 ≤ (d.vertexAngleCount v.val 2 : ℝ) * (Real.pi / 2) :=
    mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hq : 0 < (d.vertexAngleCount v.val 1 : ℝ) * d.tile.angle 1 := by
    have hqpos : (0 : ℝ) < d.vertexAngleCount v.val 1 := by
      exact_mod_cast (show 0 < d.vertexAngleCount v.val 1 by omega)
    exact mul_pos hqpos (d.tile.angle_pos 1)
  have hqb : d.vertexAngleCount v.val 1 ≤ 7 := by
    by_contra hn
    have hc : (8 : ℝ) ≤ d.vertexAngleCount v.val 1 := by
      exact_mod_cast (show 8 ≤ d.vertexAngleCount v.val 1 by omega)
    have hm := mul_le_mul_of_nonneg_right hc (d.tile.angle_pos 1).le
    linarith
  have hrb : d.vertexAngleCount v.val 2 ≤ 3 := by
    by_contra hn
    have hc : (4 : ℝ) ≤ d.vertexAngleCount v.val 2 := by
      exact_mod_cast (show 4 ≤ d.vertexAngleCount v.val 2 by omega)
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ Real.pi / 2)
    linarith
  exact ⟨_, _, _, k, hv, hqb, hrb, hkp, hkb, hs⟩

end Erdos633b.Tiling
