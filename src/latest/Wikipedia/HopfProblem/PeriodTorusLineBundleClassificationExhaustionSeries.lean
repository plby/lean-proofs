import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarAnalytic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Convergent analytic corrections on an exhaustion

Geometrically small successive corrections have genuinely analytic tails
on every member of an increasing open exhaustion.  The tails are the
actual infinite sums; convergence and analyticity are proved by the
Weierstrass bound and the two-variable locally uniform limit theorem.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusLineBundleClassificationPolydiscAnalytic
  (analyticOnNhd_of_tendstoLocallyUniformlyOn)

def correctionDifference (u : ℕ → ℂ × ℂ → ℂ) (n : ℕ) (q : ℂ × ℂ) : ℂ :=
  u (n + 1) q - u n q

def correctionTail (u : ℕ → ℂ × ℂ → ℂ) (N : ℕ) (q : ℂ × ℂ) : ℂ :=
  ∑' n, correctionDifference u (n + N) q

def correctionLimit (u : ℕ → ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  u 0 q + ∑' n, correctionDifference u n q

theorem summable_half_powers : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem correction_tail_bound {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hmono : Monotone U)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N n : ℕ) (q : ℂ × ℂ) (hq : q ∈ U N) :
    ‖correctionDifference u (n + N) q‖ ≤ (1 / 2 : ℝ) ^ n := by
  calc
    ‖correctionDifference u (n + N) q‖ ≤ (1 / 2 : ℝ) ^ (n + N) :=
      hb (n + N) q (hmono (Nat.le_add_left N n) hq)
    _ = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ N := pow_add _ _ _
    _ ≤ (1 / 2 : ℝ) ^ n := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))

theorem correction_tail_summable {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hmono : Monotone U)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) (q : ℂ × ℂ) (hq : q ∈ U N) :
    Summable (fun n => correctionDifference u (n + N) q) := by
  have hs : Summable (fun n => ‖correctionDifference u (n + N) q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => correction_tail_bound hmono hb N n q hq) summable_half_powers
  exact hs.of_norm

theorem correction_summable {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hmono : Monotone U) (hcover : ∀ q, ∃ N, q ∈ U N)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (q : ℂ × ℂ) : Summable (fun n => correctionDifference u n q) := by
  obtain ⟨N, hN⟩ := hcover q
  exact Summable.comp_nat_add (f := fun n => correctionDifference u n q) (k := N)
    (correction_tail_summable hmono hb N q hN)

/-- Every tail is a genuinely jointly analytic function on the part of the
exhaustion where all of its summands are analytic. -/
theorem correctionTail_analyticOnNhd {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hhol : ∀ n, AnalyticOnNhd ℂ (correctionDifference u n) (U n))
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) : AnalyticOnNhd ℂ (correctionTail u N) (U N) := by
  have hlim := tendstoUniformlyOn_tsum_nat
    (f := fun n => correctionDifference u (n + N)) summable_half_powers
    (fun n q hq => correction_tail_bound hmono hb N n q hq)
  apply analyticOnNhd_of_tendstoLocallyUniformlyOn (hU N) hlim.tendstoLocallyUniformlyOn
  exact Eventually.of_forall (fun M => (Finset.range M).analyticOnNhd_fun_sum
    (fun n _ => (hhol (n + N)).mono (hmono (Nat.le_add_left N n))))

theorem sum_correctionDifference (u : ℕ → ℂ × ℂ → ℂ) (N : ℕ) (q : ℂ × ℂ) :
    ∑ n ∈ Finset.range N, correctionDifference u n q = u N q - u 0 q := by
  exact Finset.sum_range_sub (fun n => u n q) N

/-- The same actual limit is a finite-stage primitive plus its analytic
tail, for every stage of the exhaustion. -/
theorem correctionLimit_eq_stage_add_tail {u : ℕ → ℂ × ℂ → ℂ}
    {U : ℕ → Set (ℂ × ℂ)} (hmono : Monotone U) (hcover : ∀ q, ∃ N, q ∈ U N)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) (q : ℂ × ℂ) : correctionLimit u q = u N q + correctionTail u N q := by
  have hs := correction_summable hmono hcover hb q
  have ht := hs.sum_add_tsum_nat_add N
  rw [sum_correctionDifference] at ht
  unfold correctionLimit correctionTail
  rw [← ht]
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
