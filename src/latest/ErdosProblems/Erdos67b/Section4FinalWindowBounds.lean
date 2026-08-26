import ErdosProblems.Erdos67b.Section4ConcreteWeightWindow

/-! # Concrete Dirichlet-window bounds for the final scalar budget -/

open scoped BigOperators
open Finset

namespace Erdos67b

theorem taoWindowMass_le_two_log {X Y N : ℕ} (hX : 1 < X)
    (hlog : 1 ≤ Real.log (X : ℝ)) :
    taoWindowMass X Y N ≤ 2 * Real.log X := by
  have hh := taoWindowMass_le_one_add_log (Y := Y) (N := N) hX
  linarith

theorem taoWindowResidueMass_le_two_log_div {r X Y N : ℕ} [NeZero r]
    (hX : 1 < X) (hY : 0 < Y) (hYN : Y ^ 2 ≤ N)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hrY : 2 * r ≤ Y ^ 2) (a : ZMod r) :
    taoWindowResidueMass X Y N a ≤ 2 * Real.log X / r := by
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne r))
  have hYsq : (0 : ℝ) < ((Y ^ 2 : ℕ) : ℝ) := by positivity
  have herr : (2 : ℝ) / ((Y ^ 2 : ℕ) : ℝ) ≤ 1 / (r : ℝ) := by
    apply (div_le_div_iff₀ hYsq hr).2
    simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).2 hrY
  calc
    _ ≤ taoWindowMass X Y N / (r : ℝ) + 2 / ((Y ^ 2 : ℕ) : ℝ) :=
      taoWindowResidueMass_le_div_add_inv hX hY hYN a
    _ ≤ (1 + Real.log X) / (r : ℝ) + 1 / r :=
      add_le_add (div_le_div_of_nonneg_right (taoWindowMass_le_one_add_log hX) hr.le) herr
    _ = (Real.log X + 2) / (r : ℝ) := by ring
    _ ≤ 2 * Real.log X / (r : ℝ) := div_le_div_of_nonneg_right (by linarith) hr.le

theorem sum_sq_taoLowCutoffResidueMass_le_log_bound
    {r X Y : ℕ} [NeZero r] (good : Finset (ZMod r))
    (hX : 1 < X) (hY : 2 ≤ Y) :
    ∑ a ∈ good, (taoLowCutoffResidueMass X Y a) ^ 2 ≤
      (1 + 2 * Real.log Y) ^ 2 / (r : ℝ) + 2 * (1 + 2 * Real.log Y) := by
  have hlow : taoLowCutoffMass X Y ≤ 1 + 2 * Real.log Y := by
    have hh := taoLowCutoffMass_le_one_add_log_sq hX hY
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hh
  have hlow0 := taoLowCutoffMass_nonneg X Y
  calc
    _ ≤ ((r : ℝ)⁻¹ * taoLowCutoffMass X Y + 2) * taoLowCutoffMass X Y :=
      sum_sq_taoLowCutoffResidueMass_le_explicit good hX hY
    _ ≤ ((r : ℝ)⁻¹ * (1 + 2 * Real.log Y) + 2) * (1 + 2 * Real.log Y) := by
      gcongr
    _ = _ := by ring

end Erdos67b
