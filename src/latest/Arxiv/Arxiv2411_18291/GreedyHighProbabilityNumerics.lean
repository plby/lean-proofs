import Arxiv.Arxiv2411_18291.StretchedExponentialTail

/-! # Uniform failure bounds for the greedy process -/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

def greedyDensityBound (M r : ℕ) : ℝ :=
  1 / (4 * (max 1 M : ℕ) * (1 + 4 * (r + 1).factorial * (max 1 M : ℕ)))

theorem greedyDensityBound_pos (M r : ℕ) : 0 < greedyDensityBound M r := by
  have hM : (0 : ℝ) < (max 1 M : ℕ) := by exact_mod_cast (lt_of_lt_of_le
    Nat.zero_lt_one (le_max_left 1 M))
  unfold greedyDensityBound
  positivity

theorem greedy_smallness_of_density_bound (M r : ℕ) {θ : ℝ}
    (hθ : θ ≤ greedyDensityBound M r) :
    (M : ℝ) * (θ + M * (4 * (r + 1).factorial * θ)) ≤ 1 / 4 := by
  by_cases hM : M = 0
  · simp only [hM, Nat.cast_zero, zero_mul]
    norm_num
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.pos_of_ne_zero hM)
  have hm : max 1 M = M := max_eq_right (by omega)
  rw [greedyDensityBound, hm] at hθ
  have hden : 0 < 4 * (M : ℝ) * (1 + 4 * (r + 1).factorial * M) := by positivity
  have hprod := (le_div_iff₀ hden).mp hθ
  nlinarith only [hprod]

theorem greedy_paper_output_bound (r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    θ ≤ 4 * (r + 1).factorial * θ ∧
      4 * (r + 1).factorial * θ ≤
        (2 : ℝ) ^ (r + 2) * (r + 1).factorial * θ := by
  have hf : (1 : ℝ) ≤ (r + 1).factorial := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hp : (4 : ℝ) ≤ (2 : ℝ) ^ (r + 2) := by
    have hh : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    rw [pow_add]
    norm_num
    linarith only [hh]
  constructor
  · have hh := mul_le_mul_of_nonneg_right hf hθ
    nlinarith only [hh, hθ]
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) hθ

theorem eventually_greedy_failure_lt_stretched_exp (M r : ℕ) {ρ β : ℝ}
    (hρ : ρ < 1) (hβ : β < 1 - ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ, (n : ℝ) ^ (-ρ) ≤ θ →
      (M : ℝ) * (n.choose r : ℝ) *
          Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) <
        Real.exp (-((n : ℝ) ^ β)) := by
  have hC : 0 < 2 * ((r + 1).factorial : ℝ) / 3 := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_polynomial_mul_exp_lt_exp (M : ℝ) r (Nat.cast_nonneg M) hC
      (show 0 < 1 - ρ by linarith) hβ] with n hn htail
  intro θ hθ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have heq : (2 * ((r + 1).factorial : ℝ) / 3) * (n : ℝ) ^ (1 - ρ) =
      2 * (r + 1).factorial * (n : ℝ) ^ (-ρ) * n / 3 := by
    rw [show 1 - ρ = -ρ + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    ring
  rw [heq] at htail
  have hexp : Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) ≤
      Real.exp (-(2 * (r + 1).factorial * (n : ℝ) ^ (-ρ) * n / 3)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hθ
      (show 0 ≤ 2 * ((r + 1).factorial : ℝ) * n / 3 by positivity)
    nlinarith only [hm]
  have hcoef : (M : ℝ) * (n.choose r : ℝ) ≤ M * (n : ℝ) ^ r := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
    exact_mod_cast Nat.choose_le_pow n r
  exact (mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)).trans_lt htail

end Arxiv2411_18291
