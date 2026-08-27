import Arxiv.Arxiv2411_18291.AsymptoticCliqueCount

/-!
# Polynomial scales for frame counts

The forbidden-vertex budget is eventually negligible whenever the rooted
clique density exponent is below one. The frame product has exactly the
accumulated density exponent, with the remaining free-vertex factor intact.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_frame_collision_bound (U m : ℕ) (hm : 0 < m) {c γ : ℝ}
    (hc : 0 < c) (hγ : γ < 1) :
    ∀ᶠ n : ℕ in atTop, (U : ℝ) * (n : ℝ) ^ (m - 1) ≤
      (c * (n : ℝ) ^ (-γ) * (n : ℝ) ^ m) / 2 := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < 1 - γ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (2 * U / c))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge] with n hn hln
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (n : ℝ) ^ (-γ) * n = (n : ℝ) ^ (1 - γ) := by
    have hr := Real.rpow_add hnpos (-γ) 1
    rw [Real.rpow_one] at hr
    calc
      _ = (n : ℝ) ^ (-γ + 1) := hr.symm
      _ = _ := by congr 1; ring
  have hsmall : (2 : ℝ) * U ≤ c * (n : ℝ) ^ (-γ) * n := by
    rw [mul_assoc, he]
    have hb := (div_le_iff₀ hc).mp hln
    simpa only [Function.comp_def, mul_comm] using hb
  have hp := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hnpos.le (m - 1))
  have hpow : (n : ℝ) * (n : ℝ) ^ (m - 1) = (n : ℝ) ^ m := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rw [mul_assoc (c * (n : ℝ) ^ (-γ)) (n : ℝ), hpow] at hp
  linarith only [hp]

theorem frame_completion_scale {x : ℝ} (hx : 0 < x) (c γ : ℝ) (m t z : ℕ) :
    (3 / 4 : ℝ) * ((c * x ^ (-γ) * x ^ m) / 2) ^ t * x ^ z =
      ((3 / 4 : ℝ) * (c / 2) ^ t) * x ^ (-(γ * t)) * x ^ (m * t + z) := by
  have he : (c * x ^ (-γ) * x ^ m) / 2 = (c / 2) * x ^ (-γ) * x ^ m := by ring
  rw [he, mul_pow, mul_pow]
  calc
    _ = ((3 / 4 : ℝ) * (c / 2) ^ t) * (x ^ (-γ)) ^ t * (x ^ (m * t) * x ^ z) := by
      rw [pow_mul]
      ring
    _ = _ := by rw [← Real.rpow_mul_natCast hx.le, ← pow_add, neg_mul]

end Arxiv2411_18291
