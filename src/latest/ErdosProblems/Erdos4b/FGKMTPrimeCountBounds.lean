/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeIntervalLower

/-! # Two-sided bounds for the literal upper-half prime count -/

namespace Erdos4b.FGKMT

noncomputable section

open Asymptotics Filter
open scoped Topology

theorem commonPinnedPrimeSet_card_le_primeCounting (x : ℕ) :
    (commonPinnedPrimeSet (x / 2) x).card ≤ Nat.primeCounting x := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  have h := mem_commonPinnedPrimeSet.mp hp
  exact Nat.mem_primesLE.mpr ⟨h.2.1, h.2.2⟩

theorem eventually_primeCounting_le_two_div_log :
    ∀ᶠ x : ℕ in atTop, (Nat.primeCounting x : ℝ) ≤ 2 * (x : ℝ) / Real.log (x : ℝ) := by
  have hne : ∀ᶠ x : ℕ in atTop, (x : ℝ) / Real.log (x : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
    exact ne_of_gt (div_pos (by linarith) (Real.log_pos hx1))
  have hratio : Tendsto (fun x : ℕ =>
      (Nat.primeCounting x : ℝ) / ((x : ℝ) / Real.log (x : ℝ))) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hne).mp
      BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  filter_upwards [(tendsto_order.mp hratio).2 2 (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with x hx hx2
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hden : 0 < (x : ℝ) / Real.log (x : ℝ) := div_pos (by linarith) (Real.log_pos hx1)
  have h := (div_lt_iff₀ hden).mp hx
  simpa only [mul_div_assoc] using h.le

theorem eventually_commonPinnedPrimeSet_card_bounds :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / (8 * Real.log (x : ℝ)) ≤ (commonPinnedPrimeSet (x / 2) x).card ∧
      ((commonPinnedPrimeSet (x / 2) x).card : ℝ) ≤ 2 * x / Real.log (x : ℝ) := by
  filter_upwards [eventually_commonPinnedPrimeSet_half_card_lower,
    eventually_primeCounting_le_two_div_log] with x hlo hhi
  have hcard : ((commonPinnedPrimeSet (x / 2) x).card : ℝ) ≤ Nat.primeCounting x := by
    exact_mod_cast commonPinnedPrimeSet_card_le_primeCounting x
  exact ⟨hlo, hcard.trans hhi⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_commonPinnedPrimeSet_card_bounds
