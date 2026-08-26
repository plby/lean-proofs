import Mathlib

/-!
# Explicit cost of the cross-block amplifying power

The elementary factorial bound suffices if block separation pays an
explicit logarithmic cost. No asymptotic factorial estimate is assumed.
-/

namespace Erdos67b

theorem ceil_ratio_bounds {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    1 ≤ (Nat.ceil (v / u) : ℝ) ∧
      (Nat.ceil (v / u) : ℝ) ≤ 2 * v / u ∧
      (Nat.ceil (v / u) : ℝ) ≤ 2 * v ∧
      (Nat.ceil (v / u) : ℝ) * u ≤ v + u := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hr1 : (1 : ℝ) ≤ v / u := (le_div_iff₀ hu0).mpr (by simpa using huv)
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ v / u)).le
  have hc2 : (Nat.ceil (v / u) : ℝ) ≤ 2 * v / u := by
    calc
      _ ≤ v / u + 1 := hc
      _ ≤ 2 * (v / u) := by linarith
      _ = 2 * v / u := by ring
  have hdiv : v / u ≤ v := (div_le_iff₀ hu0).mpr (by nlinarith)
  refine ⟨hr1.trans (Nat.le_ceil _), hc2, by linarith, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hc hu0.le
  rw [add_mul, div_mul_cancel₀ _ hu0.ne', one_mul] at hm
  exact hm

/-- Factorial square and dyadic support growth are paid by an explicit
logarithmic multiple of the current block scale. -/
theorem ceil_ratio_factorial_cost_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    {k : ℕ} (hk : k = Nat.ceil (v / u)) :
    (2 : ℝ) ^ (k + 2) * (k.factorial : ℝ) ^ 2 ≤
      4 * Real.exp (6 * v * Real.log (2 * v) / u) := by
  have hu0 : 0 < u := by linarith
  have hv1 : (1 : ℝ) ≤ v := hu.trans huv
  have hv0 : 0 < v := by linarith
  have hkb := ceil_ratio_bounds hu huv
  rw [← hk] at hkb
  have hk0 : (0 : ℝ) < k := by linarith [hkb.1]
  have hklog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkb.1
  have hlog0 : 0 ≤ Real.log (2 * v) := Real.log_nonneg (by linarith)
  have hklog : Real.log (k : ℝ) ≤ Real.log (2 * v) :=
    Real.log_le_log hk0 hkb.2.2.1
  have hlog2 : Real.log 2 ≤ Real.log (2 * v) := Real.log_le_log (by norm_num) (by linarith)
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hfac0 : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hfaclog := Real.log_le_log hfac0 hfac
  rw [Real.log_pow] at hfaclog
  have hcost : (k : ℝ) * (Real.log 2 + 2 * Real.log (k : ℝ)) ≤
      (2 * v / u) * (3 * Real.log (2 * v)) :=
    mul_le_mul hkb.2.1 (by linarith) (by positivity) (by positivity)
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4]
  push_cast
  calc
    ((k : ℝ) + 2) * Real.log 2 + 2 * Real.log (k.factorial : ℝ) ≤
        2 * Real.log 2 + (k : ℝ) * (Real.log 2 + 2 * Real.log (k : ℝ)) := by nlinarith
    _ ≤ 2 * Real.log 2 + (2 * v / u) * (3 * Real.log (2 * v)) := add_le_add le_rfl hcost
    _ = _ := by ring

theorem exp_threshold_power_le {u v alpha beta : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (halpha : 0 ≤ alpha) {k : ℕ} (hk : k = Nat.ceil (v / u)) :
    Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹ ≤
      Real.exp (-2 * (beta - alpha) * v + 2 * alpha * u) := by
  have hkb := ceil_ratio_bounds hu huv
  rw [← hk] at hkb
  have heq : Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹ =
      Real.exp (-2 * beta * v + 2 * alpha * ((k : ℝ) * u)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [heq]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hkb.2.2.2 (by positivity : 0 ≤ 2 * alpha)
  nlinarith

/-- The source moment factor decays once separation pays the factorial
cost and the two block thresholds have a positive gap. -/
theorem crossBlock_amplification_decay
    {u v alpha beta delta tau : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (halpha : 0 ≤ alpha) (_hdelta : 0 < delta) (htau : 0 ≤ tau)
    (hcost : 6 * Real.log (2 * v) / u ≤ delta) (hgap : delta ≤ beta - alpha)
    {k : ℕ} (hk : k = Nat.ceil (v / u)) :
    (Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
      (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 * (tau + Real.pi * 2 ^ (k + 2) * Real.exp u)) ≤
      32 * Real.exp 12 * (1 + Real.pi) * (tau + 1) *
        Real.exp ((1 + 2 * alpha) * u - delta * v) := by
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hexpu : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu0
  have hpow : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
  have hB : 1 ≤ (2 : ℝ) ^ (k + 2) * Real.exp u := by nlinarith
  have hlength : tau + Real.pi * 2 ^ (k + 2) * Real.exp u ≤
      (1 + Real.pi) * (tau + 1) * (2 ^ (k + 2) * Real.exp u) := by
    have hp := Real.pi_pos
    have htB := mul_le_mul_of_nonneg_left hB htau
    have htp : 0 ≤ Real.pi * tau := by positivity
    nlinarith
  let A := -2 * (beta - alpha) * v + 2 * alpha * u
  let B := 6 * v * Real.log (2 * v) / u
  have hexponent : A + B + u ≤ (1 + 2 * alpha) * u - delta * v := by
    have hpaid := mul_le_mul_of_nonneg_right hcost hv0
    have hpaid' : 6 * v * Real.log (2 * v) / u ≤ delta * v := by
      calc
        _ = (6 * Real.log (2 * v) / u) * v := by ring
        _ ≤ delta * v := hpaid
    have hgapv := mul_le_mul_of_nonneg_right hgap hv0
    dsimp only [A, B]
    nlinarith
  calc
    _ ≤ Real.exp A *
        (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 *
          ((1 + Real.pi) * (tau + 1) * (2 ^ (k + 2) * Real.exp u))) := by
      apply mul_le_mul (exp_threshold_power_le hu huv halpha hk) ?_ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hlength (by positivity)
    _ = (8 * Real.exp 12 * (1 + Real.pi) * (tau + 1) * Real.exp A * Real.exp u) *
        (2 ^ (k + 2) * (k.factorial : ℝ) ^ 2) := by ring
    _ ≤ (8 * Real.exp 12 * (1 + Real.pi) * (tau + 1) * Real.exp A * Real.exp u) *
        (4 * Real.exp B) :=
      mul_le_mul_of_nonneg_left (ceil_ratio_factorial_cost_le hu huv hk) (by positivity)
    _ = (32 * Real.exp 12 * (1 + Real.pi) * (tau + 1)) * Real.exp (A + B + u) := by
      rw [Real.exp_add (A + B) u, Real.exp_add A B]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)

/-- Enlarging the cofactor interval to width eight and shifting its scale
from `v` to `v + 1` costs only an explicit factor `4 * exp 1`. -/
theorem crossBlock_amplification_enlarged_decay
    {u v alpha beta delta tau : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (halpha : 0 ≤ alpha) (hbeta : beta ≤ 1 / 4)
    (hdelta : 0 < delta) (htau : 0 ≤ tau)
    (hcost : 6 * Real.log (2 * (v + 1)) / u ≤ delta) (hgap : delta ≤ beta - alpha)
    {k : ℕ} (hk : k = Nat.ceil ((v + 1) / u)) :
    (Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
      (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 *
        (tau + Real.pi * 2 ^ (k + 4) * Real.exp u)) ≤
      128 * Real.exp 13 * (1 + Real.pi) * (tau + 1) *
        Real.exp ((1 + 2 * alpha) * u - delta * v) := by
  have hthreshold : Real.exp (-beta * v) ^ 2 ≤
      Real.exp 1 * Real.exp (-beta * (v + 1)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hlength : tau + Real.pi * 2 ^ (k + 4) * Real.exp u ≤
      4 * (tau + Real.pi * 2 ^ (k + 2) * Real.exp u) := by
    rw [show k + 4 = (k + 2) + 2 by omega, pow_add]
    norm_num
    nlinarith
  have hsource := crossBlock_amplification_decay hu (by linarith : u ≤ v + 1)
    halpha hdelta htau hcost hgap hk
  calc
    _ ≤ (Real.exp 1 * Real.exp (-beta * (v + 1)) ^ 2 *
          (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
        (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 *
          (4 * (tau + Real.pi * 2 ^ (k + 2) * Real.exp u))) := by
      apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · exact mul_le_mul_of_nonneg_right hthreshold (by positivity)
      · exact mul_le_mul_of_nonneg_left hlength (by positivity)
    _ = (4 * Real.exp 1) *
        ((Real.exp (-beta * (v + 1)) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
          (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 *
            (tau + Real.pi * 2 ^ (k + 2) * Real.exp u))) := by ring
    _ ≤ (4 * Real.exp 1) *
        (32 * Real.exp 12 * (1 + Real.pi) * (tau + 1) *
          Real.exp ((1 + 2 * alpha) * u - delta * (v + 1))) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = (128 * Real.exp 13 * (1 + Real.pi) * (tau + 1)) *
        Real.exp ((1 + 2 * alpha) * u - delta * (v + 1)) := by
      rw [show (13 : ℝ) = 1 + 12 by norm_num, Real.exp_add 1 12]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) (by positivity)

end Erdos67b
