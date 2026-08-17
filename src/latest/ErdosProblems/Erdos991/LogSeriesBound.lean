import ErdosProblems.Erdos991.EnergyFromLog
import ErdosProblems.Erdos991.Fekete

/-!
# The finite logarithmic-series bound for Erdős 991

This module connects the shifted-inner-product moment truncation in
`Erdos991EnergyFromLog` to the ordered chordal logarithmic energy in
`Check991Fekete`.
-/

open Filter Finset Metric Set
open scoped BigOperators Topology

namespace Erdos991LogSeriesBound

noncomputable section

open Erdos988

/-- The first `K` nonconstant terms of `-log (1-q)`. -/
def truncatedLogSeries (K : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, q ^ (j + 1) / (j + 1)

lemma truncatedLogSeries_succ (K : ℕ) (q : ℝ) :
    truncatedLogSeries (K + 1) q =
      truncatedLogSeries K q + q ^ (K + 1) / (K + 1) := by
  simp [truncatedLogSeries, Finset.sum_range_succ]

lemma hasSum_logSeries {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ ↦ q ^ (j + 1) / (j + 1)) (-Real.log (1 - q)) := by
  exact Real.hasSum_pow_div_log_of_abs_lt_one (by simpa [abs_of_nonneg hq0])

/-- Every nonnegative finite truncation is bounded by the full logarithmic
series. -/
lemma truncatedLogSeries_le_neg_log_one_sub {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    truncatedLogSeries K q ≤ -Real.log (1 - q) := by
  have hsum := hasSum_logSeries hq0 hq1
  calc
    truncatedLogSeries K q =
        ∑ j ∈ Finset.range K, q ^ (j + 1) / (j + 1) := rfl
    _ ≤ ∑' j : ℕ, q ^ (j + 1) / (j + 1) :=
      hsum.summable.sum_le_tsum _ (fun j hj ↦ by positivity)
    _ = -Real.log (1 - q) := hsum.tsum_eq

/-- Chordal distance and the shifted inner product satisfy
`1-q(x,y)=|x-y|²/4`. -/
lemma one_sub_normalizedDot (x y : S2) :
    1 - normalizedDot x y = dist x y ^ 2 / 4 := by
  rw [normalizedDot, sphere2_dist_sq]
  ring

/-- The full shifted-inner-product logarithmic series is exactly twice the
chordal logarithmic kernel, up to the constant `log 2`. -/
lemma neg_log_one_sub_normalizedDot (x y : S2) (hxy : x ≠ y) :
    -Real.log (1 - normalizedDot x y) =
      2 * (-Real.log (dist x y) + Real.log 2) := by
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  rw [one_sub_normalizedDot,
    Real.log_div (pow_ne_zero 2 hdist.ne') (by norm_num), pow_two,
    Real.log_mul hdist.ne' hdist.ne',
    show Real.log (4 : ℝ) = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring]
  ring

/-- Pointwise finite-series estimate away from the diagonal. -/
lemma truncatedLogSeries_normalizedDot_le (x y : S2) (hxy : x ≠ y) (K : ℕ) :
    truncatedLogSeries K (normalizedDot x y) ≤
      2 * (-Real.log (dist x y) + Real.log 2) := by
  have hq0 := normalizedDot_nonneg x y
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have hq1 : normalizedDot x y < 1 := by
    rw [← sub_pos, one_sub_normalizedDot]
    positivity
  exact (truncatedLogSeries_le_neg_log_one_sub hq0 hq1 K).trans_eq
    (neg_log_one_sub_normalizedDot x y hxy)

/-- Removing the diagonal from `powerSum` leaves exactly the ordered-pair
sum over `P.offDiag`. -/
lemma powerSum_sub_card_eq_sum_offDiag (P : Finset S2) (k : ℕ) :
    powerSum P k - (P.card : ℝ) =
      ∑ p ∈ P.offDiag, normalizedDot p.1 p.2 ^ k := by
  classical
  have hoff :
      P.offDiag = (P ×ˢ P).filter fun p ↦ p.1 ≠ p.2 := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  have hrow (x : S2) (hx : x ∈ P) :
      (∑ y ∈ P, normalizedDot x y ^ k) =
        1 + ∑ y ∈ P.erase x, normalizedDot x y ^ k := by
    conv_lhs => rw [← Finset.insert_erase hx]
    rw [Finset.sum_insert (Finset.notMem_erase x P)]
    simp
  rw [hoff, powerSum]
  calc
    (∑ x ∈ P, ∑ y ∈ P, normalizedDot x y ^ k) - (P.card : ℝ) =
        (∑ x ∈ P,
          (1 + ∑ y ∈ P.erase x, normalizedDot x y ^ k)) -
            (P.card : ℝ) := by
      congr 1
      exact Finset.sum_congr rfl hrow
    _ = ∑ x ∈ P, ∑ y ∈ P.erase x, normalizedDot x y ^ k := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ p ∈ (P ×ˢ P).filter (fun p ↦ p.1 ≠ p.2),
        normalizedDot p.1 p.2 ^ k := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.filter_ne' P, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy, Ne.symm hxy]

/-- The power-sum truncation used by `EnergyFromLog` is the finite logarithmic
series summed over ordered distinct pairs. -/
lemma sum_offDiag_truncatedLogSeries_eq_truncatedOffDiagonalLogMoment
    (P : Finset S2) (K : ℕ) :
    (∑ p ∈ P.offDiag, truncatedLogSeries K (normalizedDot p.1 p.2)) =
      Erdos991EnergyFromLog.truncatedOffDiagonalLogMoment P K := by
  classical
  induction K with
  | zero =>
      simp [truncatedLogSeries,
        Erdos991EnergyFromLog.truncatedOffDiagonalLogMoment]
  | succ K ih =>
      rw [Erdos991EnergyFromLog.truncatedOffDiagonalLogMoment] at ih ⊢
      simp_rw [truncatedLogSeries_succ]
      rw [Finset.sum_add_distrib,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ← ih]
      congr 1
      rw [← Finset.sum_div, ← powerSum_sub_card_eq_sum_offDiag]
      norm_num [Nat.cast_add]

/-- The finite off-diagonal shifted-inner-product logarithmic moment is
controlled by the ordered chordal logarithmic energy and the exact number of
ordered distinct pairs. -/
theorem truncatedOffDiagonalLogMoment_le (P : Finset S2) (K : ℕ) :
    Erdos991EnergyFromLog.truncatedOffDiagonalLogMoment P K ≤
      2 * (Check991Fekete.orderedLogEnergy P +
        (P.card : ℝ) * (P.card - 1) * Real.log 2) := by
  classical
  rw [← sum_offDiag_truncatedLogSeries_eq_truncatedOffDiagonalLogMoment]
  have hpoint : ∀ p ∈ P.offDiag,
      truncatedLogSeries K (normalizedDot p.1 p.2) ≤
        2 * (-Real.log (dist p.1 p.2) + Real.log 2) := by
    intro p hp
    exact truncatedLogSeries_normalizedDot_le p.1 p.2
      (Finset.mem_offDiag.mp hp).2.2 K
  calc
    (∑ p ∈ P.offDiag, truncatedLogSeries K (normalizedDot p.1 p.2)) ≤
        ∑ p ∈ P.offDiag,
          2 * (-Real.log (dist p.1 p.2) + Real.log 2) := by
      exact Finset.sum_le_sum hpoint
    _ = 2 * (Check991Fekete.orderedLogEnergy P +
        (P.card : ℝ) * (P.card - 1) * Real.log 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((P.offDiag.card : ℕ) : ℝ) =
          (P.card : ℝ) * (P.card - 1) := by
        rw [Finset.offDiag_card]
        cases hP : P.card with
        | zero => norm_num
        | succ n =>
            have hn : n + 1 ≤ (n + 1) * (n + 1) := by nlinarith
            rw [Nat.cast_sub hn]
            push_cast
            ring
      have hfirst :
          (∑ p ∈ P.offDiag, 2 * -Real.log (dist p.1 p.2)) =
            2 * Check991Fekete.orderedLogEnergy P := by
        simp_rw [Check991Fekete.orderedLogEnergy, Finset.mul_sum]
      rw [hfirst, hcard]
      ring

end

end Erdos991LogSeriesBound
