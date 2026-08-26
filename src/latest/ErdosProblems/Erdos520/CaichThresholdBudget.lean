import ErdosProblems.Erdos520.ScheduledSmallEnergy

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# The exact scalar budget in Caich's small-energy step

This file uses the same parameter as the repaired quadratic-variation
argument,

`T₁(ell) = ell^10 / (ell * log ell)`.

It proves positivity, identifies the corresponding maximal-energy threshold,
and verifies summability of the two fractional-moment error terms.  These are
pure scalar facts; no probabilistic or number-theoretic input occurs here.
-/

/-- Caich's localized-energy parameter `T / (ell log ell)` for
`T(ell) = ell^10`. -/
noncomputable def caichSmallEnergyT1 (ell : ℕ) : ℝ :=
  (ell : ℝ) ^ 10 / ((ell : ℝ) * Real.log (ell : ℝ))

theorem caichSmallEnergyT1_pos {ell : ℕ} (hell : 2 ≤ ell) :
    0 < caichSmallEnergyT1 ell := by
  unfold caichSmallEnergyT1
  have hellR : (0 : ℝ) < ell := by positivity
  have hlog : 0 < Real.log (ell : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ell by omega))
  exact div_pos (pow_pos hellR _) (mul_pos hellR hlog)

/-- The exact threshold used by the high-moment block maximum. -/
theorem caichMaximalEnergyThreshold_smallEnergyT1 (ell K : ℕ) :
    caichMaximalEnergyThreshold ell K (caichSmallEnergyT1 ell) =
      Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
        (ell : ℝ) ^ ((K : ℝ) / 2) := by
  unfold caichMaximalEnergyThreshold caichSmallEnergyT1
  rw [Real.sqrt_eq_rpow]

/-- For `ell >= 2`, `log ell <= ell`, so the exact parameter is at least
`ell^8`.  This deliberately coarse lower bound already gives summability. -/
theorem natCast_pow_eight_le_caichSmallEnergyT1 {ell : ℕ} (hell : 2 ≤ ell) :
    (ell : ℝ) ^ 8 ≤ caichSmallEnergyT1 ell := by
  have hellR : (0 : ℝ) < ell := by positivity
  have hlog : 0 < Real.log (ell : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ell by omega))
  have hlogle : Real.log (ell : ℝ) ≤ (ell : ℝ) :=
    Real.log_le_self hellR.le
  unfold caichSmallEnergyT1
  apply (le_div_iff₀ (mul_pos hellR hlog)).2
  calc
    (ell : ℝ) ^ 8 * ((ell : ℝ) * Real.log (ell : ℝ)) ≤
        (ell : ℝ) ^ 8 * ((ell : ℝ) * (ell : ℝ)) := by
      gcongr
    _ = (ell : ℝ) ^ 10 := by ring

private theorem pow_eight_rpow_neg_quarter {ell : ℕ} (hell : 0 < ell) :
    ((ell : ℝ) ^ 8) ^ (-(1 : ℝ) / 4) =
      (ell : ℝ) ^ (-2 : ℝ) := by
  have hx : (0 : ℝ) ≤ ell := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

private theorem pow_eight_rpow_neg_sixth {ell : ℕ} (hell : 0 < ell) :
    ((ell : ℝ) ^ 8) ^ (-(1 : ℝ) / 6) =
      (ell : ℝ) ^ (-(4 : ℝ) / 3) := by
  have hx : (0 : ℝ) ≤ ell := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

theorem caichSmallEnergyT1_rpow_neg_quarter_le {ell : ℕ} (hell : 2 ≤ ell) :
    caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 4) ≤
      (ell : ℝ) ^ (-2 : ℝ) := by
  have hbase : (0 : ℝ) < (ell : ℝ) ^ 8 := by positivity
  calc
    caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 4) ≤
        ((ell : ℝ) ^ 8) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos hbase
        (natCast_pow_eight_le_caichSmallEnergyT1 hell) (by norm_num)
    _ = (ell : ℝ) ^ (-2 : ℝ) :=
      pow_eight_rpow_neg_quarter (by omega)

theorem caichSmallEnergyT1_rpow_neg_sixth_le {ell : ℕ} (hell : 2 ≤ ell) :
    caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 6) ≤
      (ell : ℝ) ^ (-(4 : ℝ) / 3) := by
  have hbase : (0 : ℝ) < (ell : ℝ) ^ 8 := by positivity
  calc
    caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 6) ≤
        ((ell : ℝ) ^ 8) ^ (-(1 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_nonpos hbase
        (natCast_pow_eight_le_caichSmallEnergyT1 hell) (by norm_num)
    _ = (ell : ℝ) ^ (-(4 : ℝ) / 3) :=
      pow_eight_rpow_neg_sixth (by omega)

/-- The exact two-term small-energy probability budget is summable. -/
theorem summable_caichSmallEnergyT1_budget {C : ℝ} (hC : 0 ≤ C) :
    Summable fun ell : ℕ =>
      caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 4) +
        C * caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 6) := by
  have htwo : Summable fun ell : ℕ => (ell : ℝ) ^ (-2 : ℝ) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hfourThird : Summable fun ell : ℕ =>
      (ell : ℝ) ^ (-(4 : ℝ) / 3) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hmajor := htwo.add (hfourThird.mul_left C)
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with ell hell
  have hleft_nonneg :
      0 ≤ caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 4) +
        C * caichSmallEnergyT1 ell ^ (-(1 : ℝ) / 6) := by
    exact add_nonneg
      (Real.rpow_nonneg (caichSmallEnergyT1_pos hell).le _)
      (mul_nonneg hC
        (Real.rpow_nonneg (caichSmallEnergyT1_pos hell).le _))
  rw [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg]
  exact add_le_add
    (caichSmallEnergyT1_rpow_neg_quarter_le hell)
    (mul_le_mul_of_nonneg_left
      (caichSmallEnergyT1_rpow_neg_sixth_le hell) hC)

/-- Eventual positivity in the exact form consumed by
`ScheduledSmallEnergy`. -/
theorem eventually_caichSmallEnergyT1_pos :
    ∀ᶠ ell : ℕ in atTop, 0 < caichSmallEnergyT1 ell := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with ell hell
  exact caichSmallEnergyT1_pos hell

end Problem520
end Erdos
