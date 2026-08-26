/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The endpoint-side discarded region lies between the central interval and the logarithmic boundary.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CentralIntervalMoments

namespace Erdos521

open Filter
open scoped Topology

theorem eventually_central_end_le_endpoint (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, dyadicPoint (j - Nat.sqrt j) ≤ endpointCenter C (2 ^ j) := by
  filter_upwards [eventually_mainBin_bulk C, eventually_ge_atTop 9] with j hj hj₉
  have hgap := central_bin_endpoints_strict hj₉
  have hk : j - Nat.sqrt j - 1 ∈ mainBinSet j := by
    simp only [mainBinSet, Finset.mem_Ico]
    omega
  have h := hj (j - Nat.sqrt j - 1) hk
  have heq : j - Nat.sqrt j - 1 + 1 = j - Nat.sqrt j := by omega
  simpa only [heq] using h

theorem eventually_endpoint_le_dyadic_last {C : ℝ} (hC : 0 < C) :
    ∀ᶠ j : ℕ in atTop, endpointCenter C (2 ^ j) ≤ dyadicPoint j := by
  have hlim := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
    (mul_pos hC (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  filter_upwards [hlim.eventually_ge_atTop 1] with j hj
  unfold endpointCenter dyadicPoint
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

theorem eventually_central_end_lower :
    ∀ᶠ j : ℕ in atTop, 19 / 20 ≤ dyadicPoint (j - Nat.sqrt j) := by
  have hlim : Tendsto (fun j : ℕ ↦ dyadicPoint (Nat.sqrt j)) atTop (𝓝 1) :=
    inverse_scale_point_tendsto _ two_pow_sqrt_tendsto_atTop 1
  filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (19 / 20 : ℝ) < 1)),
    eventually_ge_atTop 4] with j hj hj₄
  apply hj.le.trans (dyadicPoint_mono _)
  have h := two_sqrt_le hj₄
  omega

end Erdos521
