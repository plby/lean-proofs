import Arxiv.Arxiv2411_18291.LogNibbleCliqueCountTrend
import Arxiv.Arxiv2411_18291.LogNibbleEdgeTrend

/-! # Uniform hypotheses for logarithmic tracking down to a fixed density -/

namespace Arxiv2411_18291

structure LogNibbleParameters (k : ℕ) (a g D p₀ L : ℝ) : Prop where
  rank : 3 ≤ k
  rank_le : k ≤ 5
  error_pos : 0 < a
  graph_pos : 0 < g
  degree_pos : 0 < D
  floor_pos : 0 < p₀
  floor_le_one : p₀ ≤ 1
  floor_power : a ≤ ((2 / 5 : ℝ) * p₀) ^ k
  many_edges : 200 * (k : ℝ) ^ 3 ≤ a ^ 2 * g
  count_steps : (k : ℝ) ≤ a ^ 3 * g
  codegree_nonneg : 0 ≤ L
  codegree_bound : ((k : ℝ) ^ 2 + k) * L ≤ a ^ 2 * D / 100
  overlap_bound : L ≤ a ^ 3 * D

namespace LogNibbleParameters

variable {k : ℕ} {a g D p₀ L : ℝ} (P : LogNibbleParameters k a g D p₀ L)

include P

theorem power_bound {p : ℝ} (hp : p₀ ≤ p) : a ≤ ((2 / 5 : ℝ) * p) ^ k :=
  P.floor_power.trans (pow_le_pow_left₀ (by have h := P.floor_pos; positivity)
    (mul_le_mul_of_nonneg_left hp (by norm_num)) k)

theorem error_le_floor : a ≤ p₀ := by
  have hk : 0 < k := by have h := P.rank; omega
  have hc : (2 / 5 : ℝ) * p₀ ≤ p₀ := by have h := P.floor_pos; linarith only [h]
  have hpow : p₀ ^ k ≤ p₀ := by
    have h := mul_le_mul_of_nonneg_right
      (pow_le_one₀ P.floor_pos.le P.floor_le_one : p₀ ^ (k - 1) ≤ 1) P.floor_pos.le
    rw [← pow_succ, Nat.sub_add_cancel hk, one_mul] at h
    exact h
  exact (P.floor_power.trans (pow_le_pow_left₀
    (by have h := P.floor_pos; positivity) hc k)).trans hpow

theorem error_le_one : a ≤ 1 := P.error_le_floor.trans P.floor_le_one

theorem step_le_floor : (k : ℝ) / g ≤ p₀ := by
  have ha3 : a ^ 3 ≤ a := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_one₀ P.error_pos.le P.error_le_one : a ^ 2 ≤ 1) P.error_pos.le
    nlinarith only [hh]
  apply (div_le_iff₀ P.graph_pos).mpr
  exact (P.count_steps.trans (mul_le_mul_of_nonneg_right ha3 P.graph_pos.le)).trans
    (mul_le_mul_of_nonneg_right P.error_le_floor P.graph_pos.le)

theorem consecutive_bounds {s p : ℝ} (hs : p₀ ≤ s)
    (hstep : p - s = (k : ℝ) / g) : 0 < s ∧ s ≤ p ∧ p ≤ 2 * s ∧ p₀ ≤ p := by
  have hs0 := P.floor_pos.trans_le hs
  have hnonneg : (0 : ℝ) ≤ (k : ℝ) / g := div_nonneg (Nat.cast_nonneg _) P.graph_pos.le
  have hsp : s ≤ p := by linarith only [hstep, hnonneg]
  have hsmall := P.step_le_floor.trans hs
  exact ⟨hs0, hsp, by linarith only [hstep, hsmall], hs.trans hsp⟩

theorem point_conditions {p : ℝ} (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    LogNibbleScalarConditions k a p :=
  log_nibble_scalar_conditions P.rank P.rank_le (P.floor_pos.trans_le hp) hp1
    P.error_pos.le (P.power_bound hp)

theorem clique_lower_pos {p : ℝ} (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    0 < logNibbleCliqueLower k a g D p := by
  have hk : 0 < k := by have h := P.rank; omega
  have hp0 := P.floor_pos.trans_le hp
  have hv := ((P.point_conditions hp hp1).count_bounds hk P.degree_pos.le
    P.graph_pos.le hp0.le).1
  have hh₀ := nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0
  unfold logNibbleCliqueLower
  linarith only [hv, hh₀]

theorem clique_steps (i : ℕ) (hi : p₀ ≤ removalDensity k g (i + 1)) :
    let δu := logNibbleCliqueUpperComparison k a g D (i + 1) -
      logNibbleCliqueUpperComparison k a g D i
    let δl := logNibbleCliqueLowerComparison k a g D (i + 1) -
      logNibbleCliqueLowerComparison k a g D i;
    -nibbleCliqueSlope k D (removalDensity k g i) ≤ δu ∧
      δl ≤ -nibbleCliqueSlope k D (removalDensity k g i) ∧
      |δu| ≤ 9 * (k : ℝ) ^ 3 * D ∧ |δl| ≤ 9 * (k : ℝ) ^ 3 * D := by
  have hstep := removalDensity_difference k g i
  obtain ⟨hs, hsp, _, _⟩ := P.consecutive_bounds hi hstep
  exact logNibbleClique_comparison_step_control P.rank P.error_pos.le P.graph_pos
    P.degree_pos.le hs hsp (removalDensity_le_one k P.graph_pos i)
    (P.error_le_floor.trans hi) hstep P.count_steps

end LogNibbleParameters

end Arxiv2411_18291
