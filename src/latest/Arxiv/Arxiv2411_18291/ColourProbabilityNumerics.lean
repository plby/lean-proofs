import Arxiv.Arxiv2411_18291.TypicalityDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Comparing joint and marginal colour probabilities

Small relative errors in the reference density give a small relative error
against the square of the actual marginal probability. Raising this estimate
to any fixed bounded number of colours preserves polynomial decay.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem joint_to_marginal_error {p d t ε : ℝ} (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hεhalf : ε ≤ 1 / 2) (hpd : (1 - ε) * d ≤ p) (ht : t ≤ (1 + ε) * d ^ 2) :
    t ≤ (1 + 12 * ε) * p ^ 2 := by
  have hhalf : d / 2 ≤ p := by
    have he := mul_le_mul_of_nonneg_right hεhalf hd
    nlinarith only [he, hpd]
  have hsq := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ 1 - ε) hd) hpd 2
  have hsmall : t ≤ p ^ 2 + 3 * ε * d ^ 2 := by
    nlinarith only [ht, hsq, sq_nonneg (ε * d)]
  have hd2 : d ^ 2 ≤ 4 * p ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ d / 2) hhalf 2
    nlinarith only [hh]
  calc
    t ≤ p ^ 2 + 3 * ε * d ^ 2 := hsmall
    _ ≤ p ^ 2 + (3 * ε) * (4 * p ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hd2 (by positivity))
    _ = _ := by ring

theorem joint_power_relative_bound {p d t ε : ℝ} (M H : ℕ) (hMH : M ≤ H)
    (hd : 0 ≤ d) (ht0 : 0 ≤ t) (hε : 0 ≤ ε) (hεsmall : 12 * ε ≤ 1)
    (hpd : (1 - ε) * d ≤ p) (ht : t ≤ (1 + ε) * d ^ 2) :
    t ^ M ≤ (1 + (12 * ε) * H * 2 ^ H) * p ^ (2 * M) := by
  have htm := joint_to_marginal_error hd hε (by linarith) hpd ht
  have hbase : |(1 + 12 * ε) - 1| ≤ (12 * ε) * (1 : ℝ) := by
    rw [show (1 + 12 * ε) - 1 = 12 * ε by ring, abs_of_nonneg (by positivity), mul_one]
  have hpow := relative_pow_error (a := 1 + 12 * ε) (b := 1) (k := M)
    (by positivity) (by norm_num) (by positivity) hεsmall hbase hMH
  have hupper : (1 + 12 * ε) ^ M ≤ 1 + (12 * ε) * H * 2 ^ H := by
    have h := (abs_le.mp hpow).2
    simp only [one_pow, mul_one] at h
    linarith
  have hp2 : 0 ≤ p ^ (2 * M) := by rw [pow_mul]; positivity
  calc
    t ^ M ≤ ((1 + 12 * ε) * p ^ 2) ^ M := pow_le_pow_left₀ ht0 htm _
    _ = (1 + 12 * ε) ^ M * p ^ (2 * M) := by rw [mul_pow, ← pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hupper hp2

theorem eventually_const_mul_rpow_le (C : ℝ) {β κ : ℝ} (hκβ : κ < β) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ (-β) ≤ (n : ℝ) ^ (-κ) := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < β - κ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop C)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge] with n hn hln
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ) ^ (β - κ) * (n : ℝ) ^ (-β) :=
      mul_le_mul_of_nonneg_right hln (Real.rpow_nonneg hnpos.le _)
    _ = _ := by rw [← Real.rpow_add hnpos]; congr 1; ring

theorem eventually_colour_joint_power_bound (H : ℕ) {β κ : ℝ}
    (hβ : 0 < β) (hκβ : κ < β) :
    ∀ᶠ n : ℕ in atTop, ∀ p d t : ℝ, 0 ≤ d → 0 ≤ t →
      (1 - (n : ℝ) ^ (-β)) * d ≤ p → t ≤ (1 + (n : ℝ) ^ (-β)) * d ^ 2 →
      ∀ M ≤ H, t ^ M ≤ (1 + (n : ℝ) ^ (-κ)) * p ^ (2 * M) := by
  have hsmall := (((tendsto_rpow_neg_atTop hβ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 12).eventually
      (gt_mem_nhds (by norm_num : (12 : ℝ) * 0 < 1))
  filter_upwards [hsmall, eventually_const_mul_rpow_le (12 * H * 2 ^ H) hκβ] with n hsn hen
  intro p d t hd ht hp hpair M hMH
  have hε := Real.rpow_nonneg (Nat.cast_nonneg n) (-β)
  have hs : 12 * (n : ℝ) ^ (-β) ≤ 1 := hsn.le
  have he : (12 * (n : ℝ) ^ (-β)) * H * 2 ^ H ≤ (n : ℝ) ^ (-κ) := by
    convert hen using 1
    ring
  have hp2 : 0 ≤ p ^ (2 * M) := by rw [pow_mul]; positivity
  exact (joint_power_relative_bound M H hMH hd ht hε hs hp hpair).trans
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl he) hp2)

end Arxiv2411_18291
