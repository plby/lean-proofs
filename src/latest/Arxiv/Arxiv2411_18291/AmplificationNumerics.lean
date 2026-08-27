import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# Repetition defeats a polynomial number of tests

A fixed number of independent trials suffices when its accumulated failure
exponent exceeds the degree of the polynomial counting the tests.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem trial_union_scale {x : ℝ} (hx : 0 < x) (C κ : ℝ) (f L : ℕ) :
    x ^ f * (C * x ^ (-κ)) ^ L = C ^ L * x ^ (-(κ * L - f)) := by
  rw [mul_pow]
  have he : x ^ f * (x ^ (-κ)) ^ L = x ^ (-(κ * L - f)) := by
    rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_natCast x f, ← Real.rpow_add hx]
    congr 1
    ring
  calc
    _ = C ^ L * (x ^ f * (x ^ (-κ)) ^ L) := by ring
    _ = _ := by rw [he]

theorem eventually_trial_union_bound (C κ : ℝ) (f L : ℕ) (hgap : (f : ℝ) < κ * L) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ f * (C * (n : ℝ) ^ (-κ)) ^ L < 1 := by
  have hlim := (((tendsto_rpow_neg_atTop (by linarith : 0 < κ * L - f)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (C ^ L)).eventually
      (gt_mem_nhds (by simp : C ^ L * (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlim] with n hn hsmall
  rw [trial_union_scale (by exact_mod_cast hn : (0 : ℝ) < n)]
  exact hsmall

theorem exists_trial_number (f : ℕ) {κ : ℝ} (hκ : 0 < κ) : ∃ L : ℕ, (f : ℝ) < κ * L := by
  obtain ⟨L, hL⟩ := exists_nat_gt ((f : ℝ) / κ)
  exact ⟨L, by simpa only [mul_comm] using (div_lt_iff₀ hκ).mp hL⟩

end Arxiv2411_18291
