import Arxiv.Arxiv2411_18291.NibbleEdgeStepControl

/-! # Scalar hypotheses controlling all densities above a fixed stopping value -/

namespace Arxiv2411_18291

structure NibbleComparisonParameters (k : ℕ) (a g D p₀ L : ℝ) : Prop where
  rank : 3 ≤ k
  error_pos : 0 < a
  error_half : a ≤ 1 / 2
  graph_pos : 0 < g
  degree_pos : 0 < D
  floor_pos : 0 < p₀
  floor_le_one : p₀ ≤ 1
  floor_power : a ≤ p₀ ^ k
  small : (16 * (k : ℝ)) ^ 2 * a ≤ 1
  denominator : 16 * (k : ℝ) ^ 3 * a ≤ p₀ ^ 2
  many_edges : 16 * (k : ℝ) ^ 3 ≤ a ^ 2 * g
  codegree_nonneg : 0 ≤ L
  codegree_bound : ((k : ℝ) ^ 2 + k) * L ≤ a ^ 2 * D

namespace NibbleComparisonParameters

variable {k : ℕ} {a g D p₀ L : ℝ} (P : NibbleComparisonParameters k a g D p₀ L)

include P

theorem error_le_floor : a ≤ p₀ := by
  have hexp : k - 1 + 1 = k := by have h := P.rank; omega
  have h := mul_le_mul_of_nonneg_right
    (pow_le_one₀ P.floor_pos.le P.floor_le_one : p₀ ^ (k - 1) ≤ 1) P.floor_pos.le
  rw [← pow_succ, hexp, one_mul] at h
  exact P.floor_power.trans h

theorem power_bound {p : ℝ} (hp : p₀ ≤ p) : a ≤ p ^ k :=
  P.floor_power.trans (pow_le_pow_left₀ P.floor_pos.le hp k)

theorem denominator_bound {p : ℝ} (hp : p₀ ≤ p) : 16 * (k : ℝ) ^ 3 * a ≤ p ^ 2 :=
  P.denominator.trans (pow_le_pow_left₀ P.floor_pos.le hp 2)

theorem step_le_floor : (k : ℝ) / g ≤ p₀ := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk']
  have hk3 := mul_le_mul_of_nonneg_right hk2 (Nat.cast_nonneg k)
  have hk3n : (0 : ℝ) ≤ (k : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
  have hkg : (k : ℝ) ≤ a ^ 2 * g := by
    have h := P.many_edges
    nlinarith only [hk3, hk3n, h]
  have ha1 : a ≤ 1 := P.error_half.trans (by norm_num)
  have ha2 : a ^ 2 ≤ a := by
    have h := mul_le_mul_of_nonneg_left ha1 P.error_pos.le
    nlinarith only [h]
  apply (div_le_iff₀ P.graph_pos).mpr
  exact (hkg.trans (mul_le_mul_of_nonneg_right ha2 P.graph_pos.le)).trans
    (mul_le_mul_of_nonneg_right P.error_le_floor P.graph_pos.le)

theorem consecutive_bounds {s p : ℝ} (hs : p₀ ≤ s)
    (hstep : p - s = (k : ℝ) / g) : 0 < s ∧ s ≤ p ∧ p ≤ 2 * s ∧ p₀ ≤ p := by
  have hs0 := P.floor_pos.trans_le hs
  have hnonneg : (0 : ℝ) ≤ (k : ℝ) / g := div_nonneg (Nat.cast_nonneg _) P.graph_pos.le
  have hsp : s ≤ p := by linarith only [hstep, hnonneg]
  have hsmall := P.step_le_floor.trans hs
  exact ⟨hs0, hsp, by linarith only [hstep, hsmall], hs.trans hsp⟩

theorem edge_conditions {p : ℝ} (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    let m := nibbleDegreeMain k D p
    let u := nibbleDegreeError k a D p
    let t := nibbleEdgeScale a D p
    let h₀ := nibbleCliqueMain k g D p
    let v := nibbleCliqueError k a g D p
    0 < m ∧ 0 ≤ u ∧ 0 ≤ t ∧ a ^ 2 * D ≤ t ∧ t ≤ m ∧ u ≤ m ∧ u ^ 2 ≤ t * m ∧
      0 < h₀ ∧ v ≤ h₀ / 2 ∧ v * m ≤ t * h₀ ∧ ((k : ℝ) ^ 2 + k) * L ≤ t := by
  have hk : 0 < k := by have h := P.rank; omega
  have hp0 := P.floor_pos.trans_le hp
  have hap := P.power_bound hp
  have hden := P.denominator_bound hp
  have ha1 : a ≤ 1 := P.error_half.trans (by norm_num)
  have hwidth := nibbleEdgeScale_ge_width (a := a) P.degree_pos.le hp0 hp1
  dsimp only
  exact ⟨nibbleDegreeMain_pos P.degree_pos hp0,
    nibbleDegreeError_nonneg k P.degree_pos.le hp0.le,
    nibbleEdgeScale_nonneg P.degree_pos.le hp0.le, hwidth,
    nibbleEdgeScale_le_main hk P.error_pos.le ha1 P.degree_pos hp0 hap,
    nibbleDegreeError_le_main hk P.error_pos.le ha1 P.degree_pos hp0 hap P.small,
    nibbleDegreeError_sq_le hk P.error_pos.le P.degree_pos hp0 hap P.small,
    nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0,
    nibbleCliqueError_le_half_main hk P.error_pos.le P.error_half P.graph_pos
      P.degree_pos hp0 hap hden,
    nibbleCliqueError_degree_le hk P.graph_pos P.degree_pos hp0 hden,
    P.codegree_bound.trans hwidth⟩

theorem clique_lower_pos {p : ℝ} (hp : p₀ ≤ p) : 0 < nibbleCliqueLower k a g D p := by
  have hk : 0 < k := by have h := P.rank; omega
  exact nibbleCliqueLower_pos hk P.error_pos.le P.error_half P.graph_pos P.degree_pos
    (P.floor_pos.trans_le hp) (P.power_bound hp) (P.denominator_bound hp)

end NibbleComparisonParameters

end Arxiv2411_18291
