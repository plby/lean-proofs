import Arxiv.Arxiv2411_18291.EmbeddingCountBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative binomial counts after excluding fixed vertices

An explicit relative error controls `choose(n-a,b)` compared with `n^b/b!`.
For fixed bounded `a,b`, this error is at most `n^(-κ)` for every `κ<1`
and all sufficiently large ambient sizes.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem pow_sub_relative_lower {N M ε : ℝ} (hM : 0 ≤ M) (hMN : M ≤ N)
    (hε : 0 ≤ ε) (m : ℕ) (hsize : m * M ≤ ε * N) :
    (1 - ε) * N ^ m ≤ (N - M) ^ m := by
  obtain _ | m := m
  · simp only [pow_zero, mul_one]
    linarith
  have hN : 0 ≤ N := hM.trans hMN
  have hb := pow_add_mul_le_add_pow (a := N) (b := -M) hN (by linarith) (m + 1)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← sub_eq_add_neg] at hb
  simp only [Nat.cast_add, Nat.cast_one] at hsize
  have hp := mul_le_mul_of_nonneg_right hsize (pow_nonneg hN m)
  rw [pow_succ N m] at hb ⊢
  nlinarith

theorem shifted_choose_relative_lower (n a b : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (habn : a + b ≤ n) (hsize : (b : ℝ) * (a + b) ≤ ε * n) :
    (1 - ε) * (n : ℝ) ^ b / b.factorial ≤ ((n - a).choose b : ℝ) := by
  have hp := pow_sub_relative_lower (N := (n : ℝ)) (M := (a + b : ℕ))
    (Nat.cast_nonneg _) (by exact_mod_cast habn) hε b (by simpa only [Nat.cast_add] using hsize)
  have hd := descFactorial_extension_lower n (a + b) a (by omega) habn
  simp only [Nat.add_sub_cancel_left, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul] at hd
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos b : (0 : ℝ) < b.factorial)).mpr
  simpa only [mul_comm] using hp.trans hd

theorem shifted_choose_upper (n a b : ℕ) :
    ((n - a).choose b : ℝ) ≤ (n : ℝ) ^ b / b.factorial := by
  have h := (Nat.descFactorial_le_pow (n - a) b).trans
    (Nat.pow_le_pow_left (Nat.sub_le n a) b)
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos b : (0 : ℝ) < b.factorial)).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm] using h)

theorem eventually_uniform_shifted_choose_lower (q : ℕ) {κ : ℝ} (hκ : κ < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ a ≤ q, ∀ b ≤ q,
      (1 - (n : ℝ) ^ (-κ)) * (n : ℝ) ^ b / b.factorial ≤ ((n - a).choose b : ℝ) := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < 1 - κ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (2 * (q : ℝ) ^ 2))
  filter_upwards [eventually_ge_atTop (2 * q + 1), hlarge] with n hn hln
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨by omega, ?_⟩
  intro a ha b hb
  have haR : (a : ℝ) ≤ q := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ q := by exact_mod_cast hb
  have hscale : (n : ℝ) ^ (-κ) * n = (n : ℝ) ^ (1 - κ) := by
    rw [show 1 - κ = -κ + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  apply shifted_choose_relative_lower n a b (Real.rpow_nonneg hnpos.le _) (by omega)
  rw [hscale]
  have hprod : (b : ℝ) * (a + b) ≤ 2 * (q : ℝ) ^ 2 := by
    have hm := mul_le_mul hbR (add_le_add haR hbR) (by positivity) (Nat.cast_nonneg q)
    nlinarith only [hm]
  exact hprod.trans hln

end Arxiv2411_18291
