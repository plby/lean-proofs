import ErdosProblems.Erdos4.FGKMTGrowingGapLength

/-! Scalar budgets converting the initial configuration to the required vertex and cleanup scales. -/

namespace Erdos4.FGKMT

theorem initial_scale_product {d C x s l j σ Y : ℝ}
    (hd : 0 < d) (hC : 0 < C) (hx : 0 ≤ x) (hs : 0 < s) (hl : 0 ≤ l)
    (hY0 : 0 ≤ Y) (hσ : σ ≤ C * l / s)
    (hY : Y ≤ (d / (4800 * C * Real.log 2)) * x * s)
    (hj : l / (200 * Real.log 2) ≤ j) :
    σ * Y ≤ (d / 24) * x * j := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    _ ≤ (C * l / s) * ((d / (4800 * C * Real.log 2)) * x * s) :=
      mul_le_mul hσ hY hY0 (by positivity)
    _ = (d / 24) * x * (l / (200 * Real.log 2)) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (by positivity)

theorem initial_configuration_count_budget {σ x Y L j G K B η N M : ℝ}
    (hσ : 0 ≤ σ) (hx : 0 ≤ x) (hY : 0 ≤ Y) (hL : 0 < L) (hj : 1 ≤ j)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hX : 1 ≤ x / L) (hη : η ≤ 1 / j ^ 2)
    (hcount : N ≤ K * Y / L) (hbad : M ≤ B * Y / (L * j ^ 2))
    (hproduct : σ * Y ≤ G * x * j) :
    2 * (σ * N + 1) ≤ 2 * (K * G + 1) * x * j / L ∧
      2 * (σ * (M + η * N) + 1) ≤ 2 * ((B + K) * G + 1) * x / L := by
  have hjpos : 0 < j := by linarith
  have hn : σ * N ≤ K * G * (x * j / L) := by
    calc
      _ ≤ σ * (K * Y / L) := mul_le_mul_of_nonneg_left hcount hσ
      _ = K * (σ * Y) / L := by ring
      _ ≤ K * (G * x * j) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hproduct hK) hL.le
      _ = _ := by ring
  have hunit : 1 ≤ x * j / L := by
    have hh := mul_le_mul_of_nonneg_left hj (div_nonneg hx hL.le)
    have heq : (x / L) * j = x * j / L := by ring
    rw [heq, mul_one] at hh
    exact hX.trans hh
  have hηN : η * N ≤ K * Y / (L * j ^ 2) := by
    calc
      _ ≤ (1 / j ^ 2) * (K * Y / L) := mul_le_mul hη hcount hN (by positivity)
      _ = _ := by ring
  have hcombined : M + η * N ≤ (B + K) * Y / (L * j ^ 2) :=
    (add_le_add hbad hηN).trans_eq (by ring)
  have hmiss : σ * (M + η * N) ≤ ((B + K) * G) * (x / L) := by
    calc
      _ ≤ σ * ((B + K) * Y / (L * j ^ 2)) := mul_le_mul_of_nonneg_left hcombined hσ
      _ = (B + K) * (σ * Y) / (L * j ^ 2) := by ring
      _ ≤ (B + K) * (G * x * j) / (L * j ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hproduct (by positivity)) (by positivity)
      _ = (B + K) * G * x / (L * j) := by field_simp
      _ ≤ (B + K) * G * x / L := div_le_div_of_nonneg_left (by positivity) hL
        (by nlinarith : L ≤ L * j)
      _ = _ := by ring
  constructor
  · calc
      _ ≤ 2 * (K * G * (x * j / L) + x * j / L) := by linarith
      _ = _ := by ring
  · calc
      _ ≤ 2 * (((B + K) * G) * (x / L) + x / L) := by linarith
      _ = _ := by ring

end Erdos4.FGKMT
