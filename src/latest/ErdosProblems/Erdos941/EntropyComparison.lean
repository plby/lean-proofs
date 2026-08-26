import Mathlib

/-! # Comparing a sphere lower bound with trajectory entropy -/

namespace Erdos941.Analytic

theorem normalized_collision_inequality {c C A B H x y q : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hH : 0 < H) (hx : 1 ≤ x) (hq : 0 < q) (hqy : q ≤ y)
    (hmass : c * y ≤ H * x)
    (hcollision : H ^ 2 * q ≤ A * B * (2 * H * q + C * y ^ 2 * x)) :
    c ^ 2 * q ≤ A * B * (2 * c + C) * x ^ 3 := by
  have hy : 0 ≤ y := hq.le.trans hqy
  have hx0 : 0 ≤ x := by linarith
  have hab : 0 ≤ A * B := mul_nonneg hA hB
  have hqmass : c * q ≤ H * x := (mul_le_mul_of_nonneg_left hqy hc.le).trans hmass
  have hfirst := mul_le_mul_of_nonneg_left hqmass (show 0 ≤ 2 * c * H by positivity)
  have hmasssq := mul_self_le_mul_self (mul_nonneg hc.le hy) hmass
  have hsecond := mul_le_mul_of_nonneg_left hmasssq (mul_nonneg hC hx0)
  have hinside : c ^ 2 * (2 * H * q + C * y ^ 2 * x) ≤
      H ^ 2 * (2 * c * x + C * x ^ 3) := by nlinarith only [hfirst, hsecond]
  have hx3 : x ≤ x ^ 3 := by nlinarith [sq_nonneg (x - 1)]
  have hscale : 2 * c * x + C * x ^ 3 ≤ (2 * c + C) * x ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hx3 (show 0 ≤ 2 * c by positivity)]
  have htotal : H ^ 2 * (c ^ 2 * q) ≤ H ^ 2 * (A * B * (2 * c + C) * x ^ 3) := by
    calc
      _ = c ^ 2 * (H ^ 2 * q) := by ring
      _ ≤ c ^ 2 * (A * B * (2 * H * q + C * y ^ 2 * x)) :=
        mul_le_mul_of_nonneg_left hcollision (sq_nonneg c)
      _ = (A * B) * (c ^ 2 * (2 * H * q + C * y ^ 2 * x)) := by ring
      _ ≤ (A * B) * (H ^ 2 * (2 * c * x + C * x ^ 3)) :=
        mul_le_mul_of_nonneg_left hinside hab
      _ = (H ^ 2 * (A * B)) * (2 * c * x + C * x ^ 3) := by ring
      _ ≤ (H ^ 2 * (A * B)) * ((2 * c + C) * x ^ 3) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (sq_nonneg H) hab)
      _ = _ := by ring
  nlinarith only [htotal, sq_pos_of_pos hH]

theorem exists_small_power_gap {P Q : ℝ} (hQ : 0 < Q) (hPQ : P < Q) :
    ∃ δ : ℝ, 0 < δ ∧ P * Q ^ (6 * δ) < Q := by
  have hcont : ContinuousAt (fun δ : ℝ => P * Q ^ (6 * δ)) 0 :=
    continuousAt_const.mul ((Real.continuousAt_const_rpow hQ.ne').comp
      (continuousAt_const.mul continuousAt_id))
  have hevent : ∀ᶠ δ in nhds (0 : ℝ), P * Q ^ (6 * δ) < Q := by
    have h := hcont.eventually (gt_mem_nhds (by simpa using hPQ))
    exact h
  have hright : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  exact (hright.and (hevent.filter_mono nhdsWithin_le_nhds)).exists

end Erdos941.Analytic
