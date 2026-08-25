import ErdosProblems.Erdos1141.BurgessSubpower
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Elementary estimates for the power scales in Burgess averaging
-/

namespace Pollack17.Burgess

open Filter

theorem eventually_const_mul_rpow_le {C d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ a ≤ d * (q : ℝ) ^ b := by
  have hlarge := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with q hq hq1
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hratio : C ≤ d * (q : ℝ) ^ (b - a) := by
    simpa only [mul_comm, Function.comp_apply] using (div_le_iff₀ hd).mp hq
  calc
    _ ≤ (d * (q : ℝ) ^ (b - a)) * (q : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hq0.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring

theorem eventually_floor_rpow_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ a / 2 ≤ (⌊(q : ℝ) ^ a⌋₊ : ℝ) ∧
        (⌊(q : ℝ) ^ a⌋₊ : ℝ) ≤ (q : ℝ) ^ a := by
  have hlarge := ((tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge] with q hq
  change 2 ≤ (q : ℝ) ^ a at hq
  refine ⟨?_, Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg q) _)⟩
  have hfloor := Nat.lt_floor_add_one ((q : ℝ) ^ a)
  linarith

theorem ceil_rpow_bounds {a : ℝ} (ha : 0 ≤ a) {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) ^ a ≤ (⌈(q : ℝ) ^ a⌉₊ : ℝ) ∧
      (⌈(q : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ a := by
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hq) ha
  refine ⟨Nat.le_ceil _, ?_⟩
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg q) a)
  linarith

theorem eventually_one_add_log_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ := by
  have hcomp := eventually_const_mul_rpow_le
    (C := 1 + (δ / 2)⁻¹) (d := 1) (a := δ / 2) (b := δ) (by norm_num) (by linarith)
  filter_upwards [hcomp, eventually_ge_atTop 1] with q hq hq1
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (δ / 2) :=
    Real.one_le_rpow (by exact_mod_cast hq1) (by linarith)
  have hlog := Real.log_natCast_le_rpow_div q (half_pos hδ)
  change Real.log (q : ℝ) ≤ (q : ℝ) ^ (δ / 2) * (δ / 2)⁻¹ at hlog
  have hbound : 1 + Real.log (q : ℝ) ≤
      (1 + (δ / 2)⁻¹) * (q : ℝ) ^ (δ / 2) := by
    nlinarith
  exact hbound.trans (by simpa only [one_mul] using hq)

end Pollack17.Burgess
