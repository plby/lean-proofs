import BoundedGaps.Maynard.ConcretePrimeCountPNTRadius
import BoundedGaps.PrimeNumberTheorem.Proof.MainTheorem

/-! The unconditional prime interval factor for every fixed natural shift. -/

namespace Erdos237b

open Filter BoundedGaps.Maynard

def shiftedPrimeIntervalCount (N h : ℕ) : ℝ :=
  (primeCountTotal (2 * N + h - 1) : ℝ) - primeCountTotal (N + h - 1)

theorem shiftedPrimeIntervalCount_nonneg (N h : ℕ) : 0 ≤ shiftedPrimeIntervalCount N h := by
  apply sub_nonneg.mpr
  exact_mod_cast Nat.monotone_primeCounting (show N + h - 1 ≤ 2 * N + h - 1 by omega)

theorem abs_primeCount_add_sub_le (a h : ℕ) :
    |(primeCountTotal (a + h) : ℝ) - primeCountTotal a| ≤ h := by
  have heq : primeCountTotal (a + h) =
      primeCountTotal a + Nat.count (fun n => (a + 1 + n).Prime) h := by
    unfold primeCountTotal Nat.primeCounting Nat.primeCounting'
    rw [show a + h + 1 = a + 1 + h by omega, Nat.count_add]
  rw [heq, Nat.cast_add, add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Nat.count_le (p := fun n => (a + 1 + n).Prime) (n := h)

theorem abs_shiftedPrimeIntervalCount_sub_unshifted_le {N : ℕ} (hN : 0 < N) (h : ℕ) :
    |shiftedPrimeIntervalCount N h - (primeCountTotalInInterval N : ℝ)| ≤ 2 * h := by
  rw [shiftedPrimeIntervalCount, cast_primeCountTotalInInterval hN,
    show 2 * N + h - 1 = (2 * N - 1) + h by omega,
    show N + h - 1 = (N - 1) + h by omega]
  have ha := abs_primeCount_add_sub_le (2 * N - 1) h
  have hb := abs_primeCount_add_sub_le (N - 1) h
  have ht := abs_sub_le
    ((primeCountTotal ((2 * N - 1) + h) : ℝ) - primeCountTotal (2 * N - 1)) 0
    ((primeCountTotal ((N - 1) + h) : ℝ) - primeCountTotal (N - 1))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  have heq : (primeCountTotal ((2 * N - 1) + h) : ℝ) - primeCountTotal ((N - 1) + h) -
      (primeCountTotal (2 * N - 1) - primeCountTotal (N - 1)) =
      (primeCountTotal ((2 * N - 1) + h) - primeCountTotal (2 * N - 1)) -
        (primeCountTotal ((N - 1) + h) - primeCountTotal (N - 1)) := by ring
  rw [heq]
  exact ht.trans (by linarith)

theorem tendsto_shiftedPrimeFactor {alpha : ℝ} (halpha : 0 < alpha) (h : ℕ) :
    Tendsto (fun N : ℕ => shiftedPrimeIntervalCount N h / N *
      Real.log (engelsmaMaynardRadius alpha N)) atTop (nhds alpha) := by
  have hpnt : Tendsto (fun n : ℕ => (primeCountTotal n : ℝ) * Real.log (n : ℝ) / n)
      atTop (nhds 1) := by
    simpa only [primeCountTotal, BoundedGaps.ordinaryPrimeNumberTheorem] using
      BoundedGaps.unconditional_ordinaryPrimeNumberTheorem
  have hbase := tendsto_primeCountTotalInInterval_div_mul_log_radius_of_pnt halpha hpnt
  have hlog := tendsto_log_engelsmaMaynardRadius_div_natCast_zero halpha
  have henv : Tendsto (fun N : ℕ => (2 * (h : ℝ)) *
      |Real.log (engelsmaMaynardRadius alpha N) / N|) atTop (nhds 0) := by
    simpa using hlog.abs.const_mul (2 * (h : ℝ))
  have hdiff : Tendsto (fun N : ℕ =>
      shiftedPrimeIntervalCount N h / N * Real.log (engelsmaMaynardRadius alpha N) -
        (primeCountTotalInInterval N : ℝ) / N * Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' ?_ henv
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    have heq : shiftedPrimeIntervalCount N h / N * Real.log (engelsmaMaynardRadius alpha N) -
        (primeCountTotalInInterval N : ℝ) / N * Real.log (engelsmaMaynardRadius alpha N) =
        (shiftedPrimeIntervalCount N h - primeCountTotalInInterval N) *
          (Real.log (engelsmaMaynardRadius alpha N) / N) := by ring
    rw [heq, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_shiftedPrimeIntervalCount_sub_unshifted_le hN h)
      (abs_nonneg _)
  have hlim := hbase.add hdiff
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [] with N
  ring

end Erdos237b
