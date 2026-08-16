import ErdosProblems.Erdos6.LargeRestrictedGKernelLimit
import BoundedGaps.Maynard.ConcretePrimeCountPNTRadius
import BoundedGaps.PrimeNumberTheorem.Proof.MainTheorem

/-!
# Shifted prime interval asymptotics for an arbitrary fixed tuple
-/

namespace Erdos6.Maynard

open Filter

noncomputable section

private theorem cast_prime_filter_Ico_eq_primeCount_sub
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    (((Finset.Ico A B).filter Nat.Prime).card : ℝ) =
      (BoundedGaps.Maynard.primeCountTotal (B - 1) : ℝ) -
        (BoundedGaps.Maynard.primeCountTotal (A - 1) : ℝ) := by
  have hAeq : A - 1 + 1 = A := by omega
  have hBeq : B - 1 + 1 = B := by omega
  unfold BoundedGaps.Maynard.primeCountTotal Nat.primeCounting
    Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  simpa [hAeq, hBeq] using
    (Finset.sum_Ico_eq_sub
      (f := fun n : ℕ => if n.Prime then (1 : ℝ) else 0) hAB)

private theorem abs_primeCountTotal_add_sub_le (a h : ℕ) :
    |(BoundedGaps.Maynard.primeCountTotal (a + h) : ℝ) -
        (BoundedGaps.Maynard.primeCountTotal a : ℝ)| ≤ (h : ℝ) := by
  have hcard := cast_prime_filter_Ico_eq_primeCount_sub
    (A := a + 1) (B := a + h + 1) (by omega) (by omega)
  have hsubset :
      (Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime ⊆
        Finset.Ico (a + 1) (a + h + 1) :=
    Finset.filter_subset Nat.Prime _
  have hcardNat := Finset.card_le_card hsubset
  rw [Nat.card_Ico] at hcardNat
  have hcardReal :
      (((Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime).card : ℝ) ≤
        (h : ℝ) := by
    exact_mod_cast (show
      ((Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime).card ≤ h by
        omega)
  have hcard' :
      (((Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime).card : ℝ) =
        (BoundedGaps.Maynard.primeCountTotal (a + h) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal a : ℝ) := by
    simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using hcard
  rw [← hcard']
  rw [abs_of_nonneg (by positivity :
    0 ≤ (((Finset.Ico (a + 1) (a + h + 1)).filter Nat.Prime).card : ℝ))]
  exact hcardReal

theorem abs_tupleShiftedPrimeIntervalCount_sub_unshifted_le
    {N : ℕ} (hN : 0 < N) {H : Finset ℕ} (h : H) :
    |tupleShiftedPrimeIntervalCount N h -
        (BoundedGaps.Maynard.primeCountTotalInInterval N : ℝ)| ≤
      2 * (h.1 : ℝ) := by
  have htotal := BoundedGaps.Maynard.cast_primeCountTotalInInterval hN
  unfold tupleShiftedPrimeIntervalCount
  rw [htotal]
  have hA := abs_primeCountTotal_add_sub_le (2 * N - 1) h.1
  have hB := abs_primeCountTotal_add_sub_le (N - 1) h.1
  have h2N : 2 * N + h.1 - 1 = (2 * N - 1) + h.1 := by omega
  have hN' : N + h.1 - 1 = (N - 1) + h.1 := by omega
  rw [h2N, hN']
  have hrearrange :
      ((BoundedGaps.Maynard.primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal ((N - 1) + h.1) : ℝ)) -
          ((BoundedGaps.Maynard.primeCountTotal (2 * N - 1) : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal (N - 1) : ℝ)) =
        ((BoundedGaps.Maynard.primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal (2 * N - 1) : ℝ)) -
          ((BoundedGaps.Maynard.primeCountTotal ((N - 1) + h.1) : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal (N - 1) : ℝ)) := by ring
  rw [hrearrange]
  calc
    _ ≤ |(BoundedGaps.Maynard.primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal (2 * N - 1) : ℝ)| +
          |(BoundedGaps.Maynard.primeCountTotal ((N - 1) + h.1) : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal (N - 1) : ℝ)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le
          ((BoundedGaps.Maynard.primeCountTotal ((2 * N - 1) + h.1) : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal (2 * N - 1) : ℝ)) 0
          ((BoundedGaps.Maynard.primeCountTotal ((N - 1) + h.1) : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal (N - 1) : ℝ)))
    _ ≤ (h.1 : ℝ) + (h.1 : ℝ) := add_le_add hA hB
    _ = 2 * (h.1 : ℝ) := by ring

theorem tendsto_tupleShiftedPrimeIntervalFactor
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) (h : H) :
    Tendsto (fun N : ℕ =>
      (tupleShiftedPrimeIntervalCount N h / (N : ℝ)) *
        Real.log (maynardRadius alpha N)) atTop (nhds alpha) := by
  have hpnt : Tendsto
      (fun n : ℕ =>
        (BoundedGaps.Maynard.primeCountTotal n : ℝ) *
          Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    simpa only [BoundedGaps.Maynard.primeCountTotal,
      BoundedGaps.ordinaryPrimeNumberTheorem] using
      BoundedGaps.unconditional_ordinaryPrimeNumberTheorem
  have hunshifted :=
    BoundedGaps.Maynard.tendsto_primeCountTotalInInterval_div_mul_log_radius_of_pnt
      halpha hpnt
  have hlog :=
    BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_natCast_zero
      halpha
  have hdiff : Tendsto (fun N : ℕ =>
      (tupleShiftedPrimeIntervalCount N h / (N : ℝ)) *
          Real.log (maynardRadius alpha N) -
        ((BoundedGaps.Maynard.primeCountTotalInInterval N : ℝ) / (N : ℝ)) *
          Real.log (maynardRadius alpha N)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have henv : Tendsto (fun N : ℕ =>
        (2 * (h.1 : ℝ)) *
          |Real.log (maynardRadius alpha N) / (N : ℝ)|)
        atTop (nhds 0) := by
      simpa using hlog.abs.const_mul (2 * (h.1 : ℝ))
    apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hbound := abs_tupleShiftedPrimeIntervalCount_sub_unshifted_le
      (Nat.zero_lt_of_lt hN) h
    rw [show
        (tupleShiftedPrimeIntervalCount N h / (N : ℝ)) *
              Real.log (maynardRadius alpha N) -
            ((BoundedGaps.Maynard.primeCountTotalInInterval N : ℝ) /
              (N : ℝ)) * Real.log (maynardRadius alpha N) =
          (tupleShiftedPrimeIntervalCount N h -
              (BoundedGaps.Maynard.primeCountTotalInInterval N : ℝ)) *
            (Real.log (maynardRadius alpha N) / (N : ℝ)) by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
  have hsum := hunshifted.add hdiff
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [] with N
    ring)

end

end Erdos6.Maynard
