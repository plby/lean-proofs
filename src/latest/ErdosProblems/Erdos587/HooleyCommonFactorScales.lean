import ErdosProblems.Erdos587.CommonFactorLogScales
import ErdosProblems.Erdos587.HooleyCriticalSquare
import ErdosProblems.Erdos587.WideTerminal

/-! # The common-factor reduction loses one fixed log-log power -/

namespace Erdos587

theorem delta_common_factor_local_width_budget {q H J T Λ A : ℝ} {B : ℕ}
    (hq : 0 ≤ q) (hH : 0 < H) (hJ : 0 ≤ J) (hT : 0 < T) (hB : 0 < B)
    (hΛ : 1 ≤ Λ) (hA : A ≤ Λ) (hqH : q * H ≤ T)
    (hside : T ^ (1 / 4 : ℝ) * Λ ^ B ≤ J)
    (hprod : T ^ (3 / 4 : ℝ) * Λ ^ B ≤ H * J) :
    A * Real.sqrt q ≤ J := by
  have hh := primitive_width_density_budget hq hJ hH hT (by linarith) hqH hside
    (by simpa only [mul_comm H J] using hprod)
  have hlogpow : Λ ≤ Λ ^ B := by
    simpa only [pow_one] using pow_le_pow_right₀ hΛ (show 1 ≤ B by omega)
  calc
    A * Real.sqrt q ≤ Λ ^ B * Real.sqrt q :=
      mul_le_mul_of_nonneg_right (hA.trans hlogpow) (Real.sqrt_nonneg q)
    _ = Real.sqrt q * Λ ^ B := mul_comm _ _
    _ ≤ J := hh

theorem delta_absorb_geometric_loglog_loss {T S p : ℝ} {T₀ : ℕ} (B : ℕ)
    (hT₀T : (T₀ : ℝ) ≤ T) (hlarge : 8192 ≤ max 1 (Real.log (Real.log T)))
    (hbudget : (T₀ : ℝ) ^ p * (max 1 (Real.log (Real.log T))) ^ (B + 1) / 8192 ≤ S) :
    (T₀ : ℝ) ^ p * (max 1 (Real.log (Real.log (T₀ : ℝ)))) ^ B ≤ S := by
  let Λ := max 1 (Real.log (Real.log T))
  let Λ₀ := max 1 (Real.log (Real.log (T₀ : ℝ)))
  have hΛ₀ : 0 ≤ Λ₀ := by dsimp [Λ₀]; positivity
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have hlogs : Λ₀ ≤ Λ := delta_loglog_nat_real_mono hT₀T
  have hpow : Λ₀ ^ B ≤ Λ ^ B := pow_le_pow_left₀ hΛ₀ hlogs B
  have hextra : 8192 * Λ ^ B ≤ Λ ^ (B + 1) := by
    rw [pow_succ]
    have hh := mul_le_mul_of_nonneg_right hlarge (pow_nonneg hΛ B)
    nlinarith
  calc
    _ ≤ (T₀ : ℝ) ^ p * Λ ^ B :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) p)
    _ ≤ (T₀ : ℝ) ^ p * Λ ^ (B + 1) / 8192 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8192)).mpr
      have hh := mul_le_mul_of_nonneg_left hextra
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ T₀) p)
      nlinarith
    _ ≤ S := hbudget

end Erdos587
