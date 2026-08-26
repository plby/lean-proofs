import ErdosProblems.Erdos1164.DyadicScales

/-! # The lower in-probability order with all eventual quantifiers -/

open Filter MeasureTheory
open scoped Topology

namespace Erdos1164

private theorem dyadic_small_budget {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    (hscale : 3 ≤ a * sqrtLogTime n) :
    (discReturnBudget (2 ^ ⌈a * sqrtLogTime n⌉₊) : ℝ) ≤
      5000 * a ^ 2 * Real.log (n : ℝ) := by
  let j := ⌈a * sqrtLogTime n⌉₊
  have hj : (j : ℝ) < a * sqrtLogTime n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hj2 : (j : ℝ) + 2 ≤ 2 * a * sqrtLogTime n := by linarith
  have hsquare : ((j : ℝ) + 2) ^ 2 ≤ (2 * a * sqrtLogTime n) ^ 2 := by
    nlinarith [sqrtLogTime_nonneg n]
  rw [show (2 * a * sqrtLogTime n) ^ 2 = 4 * a ^ 2 * sqrtLogTime n ^ 2 by ring,
    sqrtLogTime_sq hn] at hsquare
  have hasquare : 9 ≤ (a * sqrtLogTime n) ^ 2 := by nlinarith
  rw [mul_pow, sqrtLogTime_sq hn] at hasquare
  have hb := dyadic_budget_upper j
  change (discReturnBudget (2 ^ j) : ℝ) ≤ _
  nlinarith

private theorem budget_square_condition {n B : ℕ} {C : ℝ}
    (hlog : 1 ≤ Real.log (n : ℝ)) (hC : 0 ≤ C)
    (hB : (B : ℝ) ≤ C * Real.log (n : ℝ))
    (hg : (C + 1) ^ 2 * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ)) :
    (B + 1) ^ 2 ≤ n := by
  have hplus : ((B + 1 : ℕ) : ℝ) ≤ (C + 1) * Real.log (n : ℝ) := by
    push_cast
    nlinarith
  have hs : (((B + 1 : ℕ) : ℝ) ^ 2) ≤ ((C + 1) * Real.log (n : ℝ)) ^ 2 := by
    have hnon : (0 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  rw [mul_pow] at hs
  exact_mod_cast hs.trans hg

private theorem dyadic_error_small {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) {n : ℕ}
    (hscale : 16 / ε ≤ a * sqrtLogTime n) :
    4 / (((2 ^ ⌈a * sqrtLogTime n⌉₊ + 2 : ℕ) : ℝ) ^ 3) ≤ ε / 4 := by
  let j := ⌈a * sqrtLogTime n⌉₊
  let x : ℝ := ((2 ^ j + 2 : ℕ) : ℝ)
  have hj : a * sqrtLogTime n ≤ (j : ℝ) := Nat.le_ceil _
  have hp : (j : ℝ) + 1 ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast dyadic_ge_index j
  have hx : 1 ≤ x := by
    dsimp only [x]
    rw [Nat.cast_add, Nat.cast_ofNat]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hdom : 16 / ε ≤ x := by
    dsimp only [x]
    rw [Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hprod : 16 ≤ ε * x := by
    have h := (div_le_iff₀ hε).mp hdom
    nlinarith
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hcube : x ≤ x ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hx2 (by linarith : 0 ≤ x)
    nlinarith
  have hcubeprod := mul_le_mul_of_nonneg_left hcube hε.le
  change 4 / x ^ 3 ≤ ε / 4
  apply (div_le_iff₀ (by positivity : 0 < x ^ 3)).mpr
  nlinarith

/-- The lower tail is small uniformly for all sufficiently large deterministic
times. The coefficient may depend on the requested error probability. -/
theorem logRadius_lower_in_probability (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      walkLaw.real {s | logRadius s n < a * sqrtLogTime n} < ε := by
  let a := Real.sqrt (ε / 1000000)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = ε / 1000000 := Real.sq_sqrt (by positivity)
  refine ⟨a * Real.log 2, mul_pos ha log_two_pos, ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ a * sqrtLogTime n) atTop atTop :=
    sqrtLogTime_tendsto.const_mul_atTop ha
  filter_upwards [eventually_ge_atTop 2, eventually_sqrtLogTime_ge 1,
    ht.eventually (eventually_ge_atTop 3), ht.eventually (eventually_ge_atTop (16 / ε)),
    eventually_log_square_le_time ((5000 * a ^ 2 + 1) ^ 2)]
    with n hn hu hscale herr hgrowth
  let j := ⌈a * sqrtLogTime n⌉₊
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    rw [← sqrtLogTime_sq (by omega : 1 ≤ n)]
    nlinarith
  have hb := dyadic_small_budget ha (by omega : 1 ≤ n) hscale
  have hcond : (discReturnBudget (2 ^ j) + 1) ^ 2 ≤ n :=
    budget_square_condition hlog (by positivity) hb hgrowth
  have htail := radius_lower_tail_real n (2 ^ j) hn hcond
  have herror := dyadic_error_small ha hε herr
  have hclock : 24 * (discReturnBudget (2 ^ j) : ℝ) / Real.log (n : ℝ) ≤ 120000 * a ^ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (n : ℝ))).mpr
    nlinarith
  have hthreshold : (a * Real.log 2) * sqrtLogTime n ≤ (j : ℝ) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right (Nat.le_ceil (a * sqrtLogTime n)) log_two_pos.le
    nlinarith
  have hsub := logRadius_lower_event_subset n j ((a * Real.log 2) * sqrtLogTime n) hthreshold
  have hmeasure := measureReal_mono (μ := walkLaw) hsub (by finiteness)
  have htotal : 120000 * a ^ 2 + ε / 4 < ε := by rw [ha2]; linarith
  exact (hmeasure.trans (htail.trans (add_le_add hclock herror))).trans_lt htotal

end Erdos1164
