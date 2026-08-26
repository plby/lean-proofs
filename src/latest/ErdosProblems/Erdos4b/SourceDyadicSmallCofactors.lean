/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicAllocationScales

/-!
# The small-cofactor cutoff for negligible boundary and tail budgets

Integer division is retained. The ratio to the full cutoff grows only
like 4^r, and the boundary-weighted size has one fewer factor 2^r.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

def smallResidualCofactorCutoff (D r : ℕ) : ℕ :=
  D * fullResidualCofactorCutoff r / 4 ^ r

theorem fourPow_eq_twoPow_mul (r : ℕ) : (4 : ℕ) ^ r = 2 ^ r * 2 ^ r := by
  simpa only [show (2 : ℕ) * 2 = 4 by norm_num] using mul_pow (2 : ℕ) 2 r

theorem two_mul_fourPow_le_scaledCofactorCutoff {D r : ℕ} (hD : 0 < D) (hr : 2 ≤ r) :
    2 * 4 ^ r ≤ D * fullResidualCofactorCutoff r := by
  have hcore : 2 ^ r ≤ core r := Nat.pow_le_pow_right (by norm_num) r.lt_two_pow_self.le
  calc
    _ ≤ r * 4 ^ r := Nat.mul_le_mul_right _ hr
    _ = 2 ^ r * 2 ^ r * r := by rw [fourPow_eq_twoPow_mul]; ring
    _ ≤ 2 ^ r * core r * r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcore)
    _ ≤ D * (2 ^ r * core r * r) := Nat.le_mul_of_pos_left _ hD
    _ = _ := rfl

theorem two_le_smallResidualCofactorCutoff {D r : ℕ} (hD : 0 < D) (hr : 2 ≤ r) :
    2 ≤ smallResidualCofactorCutoff D r :=
  (Nat.le_div_iff_mul_le (by positivity)).mpr (two_mul_fourPow_le_scaledCofactorCutoff hD hr)

theorem smallResidualCofactorCutoff_le_full (D r : ℕ) :
    smallResidualCofactorCutoff D r ≤ D * fullResidualCofactorCutoff r := Nat.div_le_self _ _

theorem smallResidualCofactorCutoff_mul_twoPow_le (D r : ℕ) :
    smallResidualCofactorCutoff D r * 2 ^ r ≤ D * core r * r := by
  have hdiv := Nat.div_mul_le_self (D * fullResidualCofactorCutoff r) (4 ^ r)
  change smallResidualCofactorCutoff D r * 4 ^ r ≤ D * fullResidualCofactorCutoff r at hdiv
  have hmul : (smallResidualCofactorCutoff D r * 2 ^ r) * 2 ^ r ≤
      (D * core r * r) * 2 ^ r := by
    simpa only [fourPow_eq_twoPow_mul, fullResidualCofactorCutoff,
      mul_assoc, mul_left_comm, mul_comm] using hdiv
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

theorem fullCofactorCutoff_le_two_mul_small {D r : ℕ} (hD : 0 < D) (hr : 2 ≤ r) :
    D * fullResidualCofactorCutoff r ≤ 2 * 4 ^ r * smallResidualCofactorCutoff D r := by
  have hmod := Nat.mod_lt (D * fullResidualCofactorCutoff r) (by positivity : 0 < 4 ^ r)
  have hdiv := Nat.mod_add_div (D * fullResidualCofactorCutoff r) (4 ^ r)
  change _ + 4 ^ r * smallResidualCofactorCutoff D r = _ at hdiv
  have hM := two_le_smallResidualCofactorCutoff hD hr
  have hmul : 4 ^ r ≤ 4 ^ r * smallResidualCofactorCutoff D r := Nat.le_mul_of_pos_right _
    (by omega)
  nlinarith

theorem full_div_smallCofactorCutoff_le {D r : ℕ} (hD : 0 < D) (hr : 2 ≤ r) :
    (D * fullResidualCofactorCutoff r : ℕ) / (smallResidualCofactorCutoff D r : ℝ) ≤
      2 * (4 : ℝ) ^ r := by
  have hM : (0 : ℝ) < smallResidualCofactorCutoff D r := by
    exact_mod_cast (show 0 < smallResidualCofactorCutoff D r by
      have := two_le_smallResidualCofactorCutoff hD hr; omega)
  apply (div_le_iff₀ hM).mpr
  exact_mod_cast fullCofactorCutoff_le_two_mul_small hD hr

theorem eventually_smallCofactor_log_weight_le {D : ℕ} (hD : 0 < D) :
    ∀ᶠ r in atTop, (smallResidualCofactorCutoff D r : ℝ) *
      (1 + Real.log (smallResidualCofactorCutoff D r)) ≤ 5 * (D : ℝ) * core r * r := by
  filter_upwards [eventually_ge_atTop 2, eventually_log_scaledResidualCofactorCutoff_le hD]
    with r hr hlog
  have hM : (0 : ℝ) < smallResidualCofactorCutoff D r := by
    exact_mod_cast (show 0 < smallResidualCofactorCutoff D r by
      have := two_le_smallResidualCofactorCutoff hD hr; omega)
  have hlogs := Real.log_le_log hM (show (smallResidualCofactorCutoff D r : ℝ) ≤
      (D * fullResidualCofactorCutoff r : ℕ) by
        exact_mod_cast smallResidualCofactorCutoff_le_full D r)
  have hlower : 1 + Real.log (smallResidualCofactorCutoff D r) ≤ 5 * (2 : ℝ) ^ r := by
    linarith
  have hmul : (smallResidualCofactorCutoff D r : ℝ) * (2 : ℝ) ^ r ≤ (D : ℝ) * core r * r :=
    by exact_mod_cast smallResidualCofactorCutoff_mul_twoPow_le D r
  have h := mul_le_mul_of_nonneg_left hlower hM.le
  nlinarith

end

end Erdos4b.SmoothParameters
