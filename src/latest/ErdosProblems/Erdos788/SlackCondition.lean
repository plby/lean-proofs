import ErdosProblems.Erdos788.TrevisanParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A logarithmic sufficient condition for the entropy slack
-/

namespace Erdos788

theorem slackThreshold_le_monomial {p r D : ℕ} (hp : 0 < p) (hr : 0 < r) :
    trevisanSlackThreshold p r D ≤
      128040 * 2 ^ D * p ^ 2 * r ^ 3 := by
  have hpr0 : 0 < p ^ 2 * r ^ 2 := by positivity
  have hpr : 1 ≤ p ^ 2 * r ^ 2 := by omega
  have hinner : 3200 * p ^ 2 * r ^ 2 + 1 ≤
      3201 * p ^ 2 * r ^ 2 := by nlinarith
  rw [trevisanSlackThreshold]
  calc
    40 * r * 2 ^ D * (3200 * p ^ 2 * r ^ 2 + 1) ≤
        40 * r * 2 ^ D * (3201 * p ^ 2 * r ^ 2) :=
      Nat.mul_le_mul_left (40 * r * 2 ^ D) hinner
    _ = 128040 * 2 ^ D * p ^ 2 * r ^ 3 := by ring

/-- The displayed logarithmic inequality implies that all reconstruction
descriptions fit below min-entropy `r+s` with `s ≤ r`. -/
theorem slackThreshold_le_pow_of_log_bound {p r D : ℕ}
    (hp : 0 < p) (hr : 0 < r)
    (hlog : Real.log 128040 + (D : ℝ) * Real.log 2 +
        2 * Real.log p + 3 * Real.log r ≤
      (r : ℝ) * Real.log p) :
    trevisanSlackThreshold p r D ≤ p ^ r := by
  have hmonoNat := slackThreshold_le_monomial (D := D) hp hr
  have hKpos : (0 : ℝ) < trevisanSlackThreshold p r D := by
    exact_mod_cast slackThreshold_pos hr
  have hmonopos : (0 : ℝ) <
      (128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) := by
    positivity
  have hpowpos : (0 : ℝ) < (p ^ r : ℕ) := by positivity
  have hKmonoR : ((trevisanSlackThreshold p r D : ℕ) : ℝ) ≤
      (128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) := by
    exact_mod_cast hmonoNat
  have hlogKmono := Real.log_le_log hKpos hKmonoR
  have hmonoExpand :
      Real.log ((128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) : ℝ) =
        Real.log 128040 + (D : ℝ) * Real.log 2 +
          2 * Real.log p + 3 * Real.log r := by
    push_cast
    calc
      Real.log ((((128040 : ℝ) * 2 ^ D) * p ^ 2) * r ^ 3) =
          Real.log (((128040 : ℝ) * 2 ^ D) * p ^ 2) +
            Real.log (r ^ 3) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log ((128040 : ℝ) * 2 ^ D) + Real.log (p ^ 2)) +
            Real.log (r ^ 3) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = ((Real.log 128040 + Real.log (2 ^ D)) + Real.log (p ^ 2)) +
            Real.log (r ^ 3) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log 128040 + (D : ℝ) * Real.log 2 +
          2 * Real.log p + 3 * Real.log r := by
            rw [Real.log_pow, Real.log_pow, Real.log_pow]
            ring
  have hpowExpand : Real.log ((p ^ r : ℕ) : ℝ) =
      (r : ℝ) * Real.log p := by
    push_cast
    rw [Real.log_pow]
  have hlogs : Real.log (trevisanSlackThreshold p r D : ℕ) ≤
      Real.log (p ^ r : ℕ) := by
    calc
      Real.log (trevisanSlackThreshold p r D : ℕ) ≤
          Real.log (128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) := hlogKmono
      _ = Real.log 128040 + (D : ℝ) * Real.log 2 +
          2 * Real.log p + 3 * Real.log r := hmonoExpand
      _ ≤ (r : ℝ) * Real.log p := hlog
      _ = Real.log (p ^ r : ℕ) := hpowExpand.symm
  have hreal := (Real.log_le_log_iff hKpos hpowpos).mp hlogs
  exact_mod_cast hreal

theorem slackExponent_le_of_log_bound {p r D : ℕ}
    (hp : 1 < p) (hr : 0 < r)
    (hlog : Real.log 128040 + (D : ℝ) * Real.log 2 +
        2 * Real.log p + 3 * Real.log r ≤
      (r : ℝ) * Real.log p) :
    trevisanSlackExponent p r D ≤ r := by
  rw [slackExponent_le_iff hp]
  exact slackThreshold_le_pow_of_log_bound (by omega) hr hlog

end Erdos788
