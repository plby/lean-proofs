/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Integral average capacities

Finite source packings use natural capacities, while their available mass is
usually estimated over the reals.  Rounding the average demand upward loses
strictly less than one per bin.
-/

noncomputable section

namespace Erdos547b.ZhaoIntegralAverageCapacity

/-- The upward-rounded average load of `total` items in `bins` bins. -/
def averageCapacity (total bins : ℕ) : ℕ :=
  ⌈(total : ℝ) / bins⌉₊

/-- Upward rounding supplies enough total integral capacity. -/
theorem total_le_mul_averageCapacity
    (total bins : ℕ) (hbins : 0 < bins) :
    total ≤ bins * averageCapacity total bins := by
  have hbinsR : (0 : ℝ) < bins := by exact_mod_cast hbins
  have hceil : (total : ℝ) / bins ≤ (averageCapacity total bins : ℝ) :=
    Nat.le_ceil _
  have hreal : (total : ℝ) ≤
      (bins : ℝ) * (averageCapacity total bins : ℝ) := by
    calc
      (total : ℝ) = (bins : ℝ) * ((total : ℝ) / bins) := by
        field_simp
      _ ≤ (bins : ℝ) * (averageCapacity total bins : ℝ) :=
        mul_le_mul_of_nonneg_left hceil hbinsR.le
  exact_mod_cast hreal

/-- The rounded average is strictly below the real average plus one. -/
theorem averageCapacity_cast_lt
    (total bins : ℕ) (hbins : 0 < bins) :
    (averageCapacity total bins : ℝ) < (total : ℝ) / bins + 1 := by
  apply Nat.ceil_lt_add_one
  positivity

/-- Charging a common additive slack in every bin preserves the packing
inequality. -/
theorem total_add_slack_le
    (total bins slack : ℕ) (hbins : 0 < bins) :
    total + bins * slack ≤ bins * (averageCapacity total bins + slack) := by
  calc
    total + bins * slack ≤
        bins * averageCapacity total bins + bins * slack :=
      Nat.add_le_add_right (total_le_mul_averageCapacity total bins hbins) _
    _ = bins * (averageCapacity total bins + slack) := by
      rw [Nat.mul_add]

/-- A real upper bound on the average transfers to the rounded natural
capacity with one unit of loss. -/
theorem averageCapacity_cast_le_of_average_add_one_le
    (total bins : ℕ) (hbins : 0 < bins) (x : ℝ)
    (h : (total : ℝ) / bins + 1 ≤ x) :
    (averageCapacity total bins : ℝ) ≤ x := by
  exact (averageCapacity_cast_lt total bins hbins).le.trans h

end Erdos547b.ZhaoIntegralAverageCapacity

#print axioms Erdos547b.ZhaoIntegralAverageCapacity.total_le_mul_averageCapacity
#print axioms Erdos547b.ZhaoIntegralAverageCapacity.averageCapacity_cast_lt
#print axioms Erdos547b.ZhaoIntegralAverageCapacity.total_add_slack_le
