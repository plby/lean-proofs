import ErdosProblems.Erdos67.StationaryPrimeAverage
import Mathlib.NumberTheory.Chebyshev

/-! # An elementary lower bound on the prime count -/

open scoped Topology BigOperators
open Filter Finset

namespace Erdos67.StationaryModel

theorem eventually_prime_count_log_lower :
    ∀ᶠ P : ℕ in atTop, (Real.log 2 / 2) * (P : ℝ) / Real.log (P : ℝ) ≤
      ((Nat.primesLE (2 * P)).card : ℝ) := by
  have hl : Tendsto (fun P : ℕ ↦ Real.log ((P : ℝ) + 1) / P) atTop (nhds 0) := by
    have hbase : Tendsto (fun P : ℕ ↦ Real.log (P : ℝ) / P) atTop (nhds 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    have hs := hbase.comp (tendsto_add_atTop_nat 1)
    have hr : Tendsto (fun P : ℕ ↦ ((P : ℝ) + 1) / P) atTop (nhds 1) := by
      have hi : Tendsto (fun P : ℕ ↦ 1 / (P : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      apply (by simpa only [add_zero] using hi.const_add 1 :
        Tendsto (fun P : ℕ ↦ 1 + 1 / (P : ℝ)) atTop (nhds 1)).congr'
      filter_upwards [eventually_gt_atTop 0] with P hP
      field_simp [(Nat.cast_pos.mpr hP : (0 : ℝ) < P).ne']
    have hm := hs.mul hr
    apply (by simpa using hm : Tendsto
      (fun P : ℕ ↦ (Real.log ((P + 1 : ℕ) : ℝ) / ((P + 1 : ℕ) : ℝ)) *
        (((P : ℝ) + 1) / P)) atTop (nhds 0)).congr'
    filter_upwards with P
    push_cast
    field_simp [show ((P : ℝ) + 1) ≠ 0 by positivity]
  have hsmall := hl.eventually (gt_mem_nhds (show (0 : ℝ) < Real.log 2 / 2 by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 2] with P hsmall hP
  have hPR : (0 : ℝ) < P := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hnum := (div_lt_iff₀ hPR).mp hsmall
  calc
    _ ≤ ((P : ℝ) * Real.log 2 - Real.log ((P : ℝ) + 1)) / Real.log (P : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlog.le
      nlinarith
    _ ≤ (Nat.primeCounting P : ℝ) := Chebyshev.pi_ge P
    _ = ((Nat.primesLE P).card : ℝ) := by rw [Nat.primesLE_card_eq_primeCounting]
    _ ≤ _ := Nat.cast_le.mpr (card_le_card (Nat.primesLE_mono (by omega)))

end Erdos67.StationaryModel
