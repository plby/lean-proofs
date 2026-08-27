import Arxiv.Arxiv2411_18291.ShiftedChooseBounds

/-! # Polynomial lower bounds for the paper's binomial density scales -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_choose_ge_half_power (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ d / (2 * d.factorial) ≤ (n.choose d : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 * d ^ 2 + d + 1)] with n hn
  have hnat : 2 * d ^ 2 ≤ n := by omega
  have hreal : 2 * (d : ℝ) ^ 2 ≤ n := by exact_mod_cast hnat
  have h := shifted_choose_relative_lower n 0 d (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by omega) (by push_cast; nlinarith only [hreal])
  simp only [Nat.sub_zero] at h
  calc
    _ = (1 - (1 / 2 : ℝ)) * (n : ℝ) ^ d / d.factorial := by ring
    _ ≤ _ := h

theorem eventually_binomial_density_lower (d : ℕ) (η : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ ρ : ℝ, (n : ℝ) ^ (-η) ≤ ρ →
      (1 / (2 * (d.factorial : ℝ))) * (n : ℝ) ^ ((d : ℝ) - η) ≤ ρ * (n.choose d : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_choose_ge_half_power d]
    with n hn hchoose
  intro ρ hρ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ0 : 0 ≤ ρ := (Real.rpow_pos_of_pos hn0 (-η)).le.trans hρ
  calc
    _ = (n : ℝ) ^ (-η) * ((n : ℝ) ^ d / (2 * d.factorial)) := by
      rw [show (d : ℝ) - η = -η + d by ring, Real.rpow_add hn0, Real.rpow_natCast]
      ring
    _ ≤ _ := mul_le_mul hρ hchoose (by positivity) hρ0

theorem three_le_clique_size {q r : ℕ} (hr : 2 ≤ r) (hqr : r < q) : 3 ≤ q.choose r := by
  have h := Nat.choose_le_choose r (show r + 1 ≤ q by omega)
  rw [Nat.choose_succ_self_right] at h
  omega

end Arxiv2411_18291
