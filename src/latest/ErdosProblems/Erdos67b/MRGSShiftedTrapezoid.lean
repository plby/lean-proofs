import ErdosProblems.Erdos67b.MRGSPowerSumFinal

/-!
# A shifted composite-trapezoid identity

This file records the exact telescoping identity needed to apply the
one-cell complex trapezoidal estimate only after an arbitrary natural
cutoff.  It is deliberately independent of the logarithmic phase and of
the analytic estimates used later.
-/

open scoped BigOperators Interval
open Finset Set MeasureTheory intervalIntegral

namespace Erdos67b

noncomputable section

private theorem sum_Ico_trapezoidal_endpoints
    (f : ℝ → ℂ) {K M : ℕ} (hKM : K ≤ M) :
    (∑ n ∈ Finset.Ico K M,
        (f (n : ℝ) + f ((n + 1 : ℕ) : ℝ)) / 2) +
        (f (M : ℝ) - f (K : ℝ)) / 2 =
      ∑ n ∈ Finset.Ioc K M, f (n : ℝ) := by
  induction M, hKM using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
      rw [Finset.sum_Ico_succ_top hKM, Finset.sum_Ioc_succ_top hKM, ← ih]
      ring

/-- Exact shifted composite-trapezoid identity.  The discrete sum uses the
right endpoints `K < n ≤ M`, while the cell errors are indexed by
`K ≤ n < M`; the remaining half-endpoint term accounts for this shift. -/
theorem sum_Ioc_sub_integral_eq_sum_trapezoidal_cell_error
    (f : ℝ → ℂ) {K M : ℕ} (hKM : K ≤ M)
    (hint : ∀ n ∈ Finset.Ico K M,
      IntervalIntegrable f volume (n : ℝ) ((n + 1 : ℕ) : ℝ)) :
    (∑ n ∈ Finset.Ioc K M, f (n : ℝ)) -
        (∫ x in (K : ℝ)..(M : ℝ), f x) =
      (∑ n ∈ Finset.Ico K M,
        ((f (n : ℝ) + f ((n + 1 : ℕ) : ℝ)) / 2 -
          ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x)) +
        (f (M : ℝ) - f (K : ℝ)) / 2 := by
  have hintegral :
      (∑ n ∈ Finset.Ico K M,
          ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x) =
        ∫ x in (K : ℝ)..(M : ℝ), f x := by
    have hsegments := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (f := f) (μ := volume) (a := fun n : ℕ ↦ (n : ℝ)) hKM
      (fun n hn ↦ hint n (by
        simpa only [Finset.mem_Ico, Set.mem_Ico] using hn))
    simpa only [Nat.cast_add, Nat.cast_one] using hsegments
  have hendpoints := sum_Ico_trapezoidal_endpoints f hKM
  rw [Finset.sum_sub_distrib, hintegral, ← hendpoints]
  ring

end

end Erdos67b
