import Arxiv.Arxiv2411_18291.AsymptoticNibbleParameters
import Arxiv.Arxiv2411_18291.SmallSupportBoundedness

/-! # Fixed finite supports satisfy every sublinear power boundedness scale -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_const_lt_scaled_decay (K : ℝ) {C η : ℝ}
    (hC : 0 < C) (hη : η < 1) :
    ∀ᶠ n : ℕ in atTop, K < C * (n : ℝ) ^ (-η) * n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_scaled_rpow_le (K + 1) hC (show (0 : ℝ) < 1 - η by linarith)]
    with n hn hbound
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [Real.rpow_zero, mul_one] at hbound
  calc
    K < K + 1 := by linarith
    _ ≤ C * (n : ℝ) ^ (1 - η) := hbound
    _ = C * (n : ℝ) ^ (-η) * n := by
      rw [show 1 - η = -η + 1 by ring, Real.rpow_add hn0, Real.rpow_one, mul_assoc]

end Arxiv2411_18291
