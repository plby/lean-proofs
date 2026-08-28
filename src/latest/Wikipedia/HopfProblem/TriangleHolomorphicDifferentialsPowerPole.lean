import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# The pole bound for a cyclic cubic differential

An analytic numerator divided by `t ^ 2` is genuinely meromorphic, with order
at least `-2`.  The scalar pullback calculation below uses the actual power
map `t = s ^ m` and its derivative coefficient `m * s ^ (m - 1)`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- An analytic numerator divided by a coordinate power is meromorphic. -/
theorem meromorphicAt_div_coordinate_pow {H : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (n : ℕ) :
    MeromorphicAt (fun t => H t / t ^ n) 0 :=
  hH.meromorphicAt.div (analyticAt_id.pow n).meromorphicAt

/-- The displayed denominator gives the actual meromorphic-order bound. -/
theorem meromorphicOrderAt_div_coordinate_pow_ge {H : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (n : ℕ) :
    -(n : WithTop ℤ) ≤ meromorphicOrderAt (fun t => H t / t ^ n) 0 := by
  change -(n : WithTop ℤ) ≤ meromorphicOrderAt (H / (fun t : ℂ => t ^ n)) 0
  rw [meromorphicOrderAt_div (g := fun t : ℂ => t ^ n)
    hH.meromorphicAt (analyticAt_id.pow n).meromorphicAt]
  have hpow : meromorphicOrderAt (fun t : ℂ => t ^ n) 0 = (n : WithTop ℤ) := by
    have hmer : MeromorphicAt (fun t : ℂ => t ^ n) 0 :=
      (analyticAt_id.pow n).meromorphicAt
    apply (meromorphicOrderAt_eq_int_iff hmer).2
    refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
    exact Filter.Eventually.of_forall fun t => by
      simp only [sub_zero, zpow_natCast, smul_eq_mul, mul_one]
  rw [hpow]
  simpa only [sub_eq_add_neg, zero_add, add_zero, add_comm] using
    add_le_add_right hH.meromorphicOrderAt_nonneg (-(n : WithTop ℤ))

/-- The normalized analytic numerator pulls back as a cubic coefficient.
This is valid for every `m ≥ 3`, including the actual elliptic orders `3,4`. -/
theorem cubic_power_pullback_identity (m : ℕ) (hm : 3 ≤ m)
    (s h : ℂ) (hs : s ≠ 0) :
    (m : ℂ) ^ 3 * s ^ (m - 3) * h =
      ((m : ℂ) * s ^ (m - 1)) ^ 3 * (h / (s ^ m) ^ 2) := by
  have hpow : s ^ (m - 3) * (s ^ m) ^ 2 = (s ^ (m - 1)) ^ 3 := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    omega
  rw [← mul_div_assoc, eq_div_iff (pow_ne_zero 2 (pow_ne_zero m hs))]
  calc
    _ = (m : ℂ) ^ 3 * (s ^ (m - 3) * (s ^ m) ^ 2) * h := by ring
    _ = ((m : ℂ) * s ^ (m - 1)) ^ 3 * h := by rw [hpow, mul_pow]

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
