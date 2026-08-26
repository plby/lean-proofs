import ErdosProblems.Erdos421.ClippedPrimeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # A logarithmic number of sufficiently narrow prime blocks -/

namespace Erdos421

def primePartitionDepth (Z : ℕ) : ℕ := Nat.log 2 Z + 1

noncomputable def primePartitionCount (X : ℝ) : ℕ := ⌈(Real.log X) ^ (10 : ℕ)⌉₊

theorem primePartitionDepth_cover (Z : ℕ) : Z < 2 ^ primePartitionDepth Z :=
  Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) Z

theorem primePartitionDepth_le {Z : ℕ} (hZ : 0 < Z) {X : ℝ}
    (hZX : (Z : ℝ) ≤ X) (hlog : 1 ≤ Real.log X) :
    (primePartitionDepth Z : ℝ) ≤ 3 * Real.log X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hb : (Nat.log 2 Z : ℝ) ≤ Real.log Z / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb Z 2
  have hlogZ : Real.log Z ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hZ) hZX
  have hr : Real.log X / Real.log 2 ≤ 2 * Real.log X := by
    apply (div_le_iff₀ hlog2).mpr
    nlinarith
  have hbound := hb.trans ((div_le_div_of_nonneg_right hlogZ hlog2.le).trans hr)
  simp only [primePartitionDepth, Nat.cast_add, Nat.cast_one]
  linarith

theorem primePartitionCount_pos {X : ℝ} (hlog : 1 ≤ Real.log X) : 0 < primePartitionCount X := by
  have hp : 0 < (Real.log X) ^ (10 : ℕ) := by positivity
  exact Nat.one_le_ceil_iff.mpr hp

theorem primePartitionCount_le {X : ℝ} (hlog : 1 ≤ Real.log X) :
    (primePartitionCount X : ℝ) ≤ 2 * (Real.log X) ^ (10 : ℕ) := by
  have hp : 1 ≤ (Real.log X) ^ (10 : ℕ) := one_le_pow₀ hlog
  have hc := Nat.ceil_lt_add_one (show 0 ≤ (Real.log X) ^ (10 : ℕ) by positivity)
  change (primePartitionCount X : ℝ) < _ at hc
  linarith

theorem primePartitionCount_inv_le {X : ℝ} (hlog : 1 ≤ Real.log X) :
    (primePartitionCount X : ℝ)⁻¹ ≤ ((Real.log X) ^ (10 : ℕ))⁻¹ := by
  exact inv_anti₀ (by positivity) (Nat.le_ceil _)

theorem primePartition_size_le {Z : ℕ} (hZ : 0 < Z) {X : ℝ}
    (hZX : (Z : ℝ) ≤ X) (hlog : 1 ≤ Real.log X) :
    ((primePartitionDepth Z * primePartitionCount X : ℕ) : ℝ) ≤ 6 * (Real.log X) ^ (11 : ℕ) := by
  rw [Nat.cast_mul]
  calc
    _ ≤ (3 * Real.log X) * (2 * (Real.log X) ^ (10 : ℕ)) :=
      mul_le_mul (primePartitionDepth_le hZ hZX hlog) (primePartitionCount_le hlog)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end Erdos421
