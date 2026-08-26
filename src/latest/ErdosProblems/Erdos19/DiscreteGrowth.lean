import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # An elementary bound for the cumulative reservoir-load recurrence -/

namespace Erdos19

theorem affine_growth_le_geometric (S : ℕ → ℝ) (x c : ℝ)
    (hx : 0 ≤ x) (hc : 0 ≤ c) (hzero : S 0 = 0) (N : ℕ)
    (hstep : ∀ i < N, S (i + 1) ≤ (1 + x) * S i + c) :
    ∀ i ≤ N, S i ≤ c * i * (1 + x) ^ i := by
  intro i
  induction i with
  | zero => intro _; simp [hzero]
  | succ i ih =>
    intro hi
    have hiN : i < N := by omega
    have hprev := ih (by omega)
    have hone : 1 ≤ (1 + x) ^ (i + 1) := one_le_pow₀ (by linarith)
    calc
      S (i + 1) ≤ (1 + x) * S i + c := hstep i hiN
      _ ≤ (1 + x) * (c * i * (1 + x) ^ i) + c := by
        have hm := mul_le_mul_of_nonneg_left hprev (show 0 ≤ 1 + x by linarith only [hx])
        linarith only [hm]
      _ ≤ (1 + x) * (c * i * (1 + x) ^ i) + c * (1 + x) ^ (i + 1) := by
        have hm := mul_le_mul_of_nonneg_left hone hc
        linarith only [hm]
      _ = c * (i + 1) * (1 + x) ^ (i + 1) := by rw [pow_succ]; ring
      _ = c * (↑(i + 1) : ℝ) * (1 + x) ^ (i + 1) := by push_cast; rfl

theorem affine_growth_le_exponential (S : ℕ → ℝ) (b c : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hzero : S 0 = 0) (N : ℕ) (hN : 0 < N)
    (hstep : ∀ i < N, S (i + 1) ≤ (1 + b / N) * S i + c) :
    ∀ i ≤ N, S i ≤ c * N * Real.exp b := by
  intro i hi
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ b / N := div_nonneg hb hNR.le
  have hg := affine_growth_le_geometric S (b / N) c hx hc hzero N hstep i hi
  have hpow : (1 + b / N) ^ i ≤ Real.exp ((b / N) * i) := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + b / N)
      (by simpa only [add_comm] using Real.add_one_le_exp (b / N)) i
    simpa only [← Real.exp_nat_mul, mul_comm] using h
  have hiR : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hexponent : (b / N) * i ≤ b := by
    calc
      (b / N) * i ≤ (b / N) * N := mul_le_mul_of_nonneg_left hiR hx
      _ = b := by field_simp
  calc
    S i ≤ c * i * (1 + b / N) ^ i := hg
    _ ≤ c * i * Real.exp ((b / N) * i) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ c * N * Real.exp b := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hiR hc)
        (Real.exp_le_exp.mpr hexponent) (Real.exp_nonneg _) (by positivity)

#print axioms affine_growth_le_exponential

end Erdos19
