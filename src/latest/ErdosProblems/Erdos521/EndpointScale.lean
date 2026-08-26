/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Elementary estimates at logarithmic distance from the endpoints.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GeometricVariance

namespace Erdos521

open Filter
open scoped BigOperators Topology

theorem geometricVariance_mul_one_sub_sq (x : ℝ) (N : ℕ) :
    geometricVariance x N * (1 - x ^ 2) = 1 - x ^ (2 * N) := by
  simpa only [geometricVariance, pow_mul] using geom_sum_mul_neg (x ^ 2) N

theorem geometricVariance_le_count {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (N : ℕ) :
    geometricVariance x N ≤ N := by
  calc
    geometricVariance x N ≤ ∑ _ ∈ Finset.range N, (1 : ℝ) :=
      Finset.sum_le_sum fun _ _ ↦ pow_le_one₀ hx₀ hx₁
    _ = _ := by simp

theorem geometricVariance_lower {x : ℝ} (hx₁ : x < 1) (N : ℕ)
    (htail : x ^ (2 * N) ≤ 1 / 2) :
    (4 * (1 - x))⁻¹ ≤ geometricVariance x N := by
  have hV := geometricVariance_nonneg x N
  have hid := geometricVariance_mul_one_sub_sq x N
  rw [inv_eq_one_div, div_le_iff₀ (by positivity : 0 < 4 * (1 - x))]
  have hsq : 1 - x ^ 2 ≤ 2 * (1 - x) := by nlinarith [sq_nonneg (1 - x)]
  have hmul := mul_le_mul_of_nonneg_left hsq hV
  nlinarith

theorem pow_le_exp_nat_mul {y u : ℝ} (hy : 0 ≤ y) (hu : y ≤ 1 + u) (k : ℕ) :
    y ^ k ≤ Real.exp ((k : ℝ) * u) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ hy
  exact hu.trans (by simpa only [add_comm] using Real.add_one_le_exp u)

/-- The logarithmic endpoint scale, with positive constants chosen later. -/
noncomputable def endpointCenter (a : ℝ) (n : ℕ) : ℝ := 1 - a * Real.log n / n

noncomputable def endpointRadius (b : ℝ) (n : ℕ) : ℝ := b * Real.log n / n

theorem endpointCenter_tail_le {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n)
    (hx : 0 ≤ endpointCenter a n) :
    endpointCenter a n ^ (2 * (n + 1)) ≤ (n : ℝ) ^ (-2 * a) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := pow_le_exp_nat_mul (u := -(a * Real.log n / n)) hx
    (by dsimp [endpointCenter]; linarith) (2 * (n + 1))
  apply h.trans
  rw [Real.rpow_def_of_pos hn₀]
  apply Real.exp_le_exp.mpr
  push_cast
  have hq : 0 ≤ a * Real.log n / n := by positivity
  have hmul : (n : ℝ) * (a * Real.log n / n) = a * Real.log n := by field_simp
  nlinarith

theorem geometricVariance_endpoint_lower {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 < n)
    (hx : 0 ≤ endpointCenter a n) (htail : (n : ℝ) ^ (-2 * a) ≤ 1 / 2) :
    (n : ℝ) / (4 * a * Real.log n) ≤ geometricVariance (endpointCenter a n) (n + 1) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hx₁ : endpointCenter a n < 1 := by
    unfold endpointCenter
    exact sub_lt_self _ (by positivity)
  have h := geometricVariance_lower hx₁ (n + 1)
    ((endpointCenter_tail_le ha.le (by omega) hx).trans htail)
  convert h using 1
  unfold endpointCenter
  field_simp
  ring

theorem geometricVariance_endpoint_upper {a b : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hy : 0 ≤ endpointCenter a n + 4 * endpointRadius b n) :
    geometricVariance (endpointCenter a n + 4 * endpointRadius b n) (2 * n + 1) ≤
      3 * n * (n : ℝ) ^ (4 * max (4 * b - a) 0) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  let u := max (4 * b - a) 0 * Real.log n / n
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hyu : endpointCenter a n + 4 * endpointRadius b n ≤ 1 + u := by
    have hmul := mul_le_mul_of_nonneg_right (le_max_left (4 * b - a) 0)
      (div_nonneg hlog hn₀.le)
    dsimp [endpointCenter, endpointRadius, u]
    calc
      1 - a * Real.log n / n + 4 * (b * Real.log n / n) =
          1 + (4 * b - a) * (Real.log n / n) := by ring
      _ ≤ 1 + max (4 * b - a) 0 * (Real.log n / n) := add_le_add le_rfl hmul
      _ = _ := by ring
  have hpow (k : ℕ) (hk : k < 2 * n + 1) :
      (endpointCenter a n + 4 * endpointRadius b n) ^ (2 * k) ≤
        (n : ℝ) ^ (4 * max (4 * b - a) 0) := by
    apply (pow_le_exp_nat_mul hy hyu (2 * k)).trans
    rw [Real.rpow_def_of_pos hn₀]
    apply Real.exp_le_exp.mpr
    have hk' : (k : ℝ) ≤ 2 * n := by exact_mod_cast (show k ≤ 2 * n by omega)
    have hmul := mul_le_mul_of_nonneg_right hk' hu
    have hid : (n : ℝ) * u = max (4 * b - a) 0 * Real.log n := by
      dsimp [u]
      field_simp
    push_cast
    nlinarith
  calc
    geometricVariance (endpointCenter a n + 4 * endpointRadius b n) (2 * n + 1) ≤
        ∑ _ ∈ Finset.range (2 * n + 1), (n : ℝ) ^ (4 * max (4 * b - a) 0) :=
      Finset.sum_le_sum fun k hk ↦ hpow k (Finset.mem_range.mp hk)
    _ = (2 * n + 1) * (n : ℝ) ^ (4 * max (4 * b - a) 0) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 * n + 1 ≤ 3 * n by omega))
      (Real.rpow_nonneg hn₀.le _)

theorem endpointCenter_tendsto (a : ℝ) : Tendsto (endpointCenter a) atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ ↦ 1 - a * Real.log n / n) atTop (𝓝 1)
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub (h.const_mul a)
  simpa only [endpointCenter, mul_zero, sub_zero, mul_div_assoc, Function.comp_apply, id_eq] using h'

theorem eventually_endpointCenter_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ endpointCenter a n ∧ endpointCenter a n < 1 := by
  have h := (endpointCenter_tendsto a).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [h, eventually_ge_atTop 2] with n hx hn
  refine ⟨hx.le, ?_⟩
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact sub_lt_self _ (by positivity)

theorem eventually_geometricVariance_endpoint_lower {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (4 * a * Real.log n) ≤ geometricVariance (endpointCenter a n) (n + 1) := by
  have hpow := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0 : ℝ) < 2) ha)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have htail := hpow.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_endpointCenter_bounds ha, htail, eventually_ge_atTop 2]
    with n hx ht hn
  apply geometricVariance_endpoint_lower ha (by omega) (by linarith [hx.1])
  simpa only [neg_mul, Function.comp_apply] using ht.le

noncomputable def endpointThreshold (τ : ℝ) (n : ℕ) : ℕ := ⌈τ * Real.log n⌉₊

theorem endpointThreshold_pow_lower (τ : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (τ * Real.log 4) ≤ (4 : ℝ) ^ endpointThreshold τ n := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hceil : τ * Real.log n ≤ (endpointThreshold τ n : ℝ) := Nat.le_ceil _
  rw [Real.rpow_def_of_pos hn₀, ← Real.exp_log (by norm_num : (0 : ℝ) < 4),
    ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hceil (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
  simpa only [Real.log_exp, mul_assoc, mul_comm, mul_left_comm] using hmul

end Erdos521
