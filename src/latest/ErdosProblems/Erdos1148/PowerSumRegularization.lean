import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Power sums below the pole: a regularized value and a uniform remainder -/

namespace Erdos1148.DukeArithmetic

open Filter Topology MeasureTheory Set

lemma neg_rpow_antitoneOn_one {s : ℝ} (hs : 0 ≤ s) :
    AntitoneOn (fun x : ℝ => x ^ (-s)) (Ici 1) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) hxy
    (neg_nonpos.mpr hs)

noncomputable def powerSumDiscrepancy (s : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ (-s) - ∫ x : ℝ in (n + 1)..(n + 2), x ^ (-s)

lemma powerSumDiscrepancy_bounds {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ powerSumDiscrepancy s n ∧
      powerSumDiscrepancy s n ≤ (n + 1 : ℝ) ^ (-s) - (n + 2 : ℝ) ^ (-s) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s))
      (Icc (n + 1 : ℝ) ((n + 1 : ℝ) + (1 : ℕ))) :=
    (neg_rpow_antitoneOn_one hs).mono (fun x hx => by
      change 1 ≤ x
      exact le_trans (le_add_of_nonneg_left (Nat.cast_nonneg n)) hx.1)
  have hu := hanti.integral_le_sum
  have hl := hanti.sum_le_integral
  norm_num only [Finset.sum_range_one, Nat.cast_one, Nat.cast_zero, add_zero,
    zero_add] at hu hl
  have heq : (n + 1 : ℝ) + 1 = n + 2 := by ring
  rw [heq] at hu hl
  exact ⟨sub_nonneg.mpr hu, sub_le_sub_left hl _⟩

lemma powerSumDiscrepancy_sum_le {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∑ k ∈ Finset.range n, powerSumDiscrepancy s k ≤ 1 - (n + 1 : ℝ) ^ (-s) := by
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        ((k + 1 : ℝ) ^ (-s) - (k + 2 : ℝ) ^ (-s)) :=
      Finset.sum_le_sum (fun k _ => (powerSumDiscrepancy_bounds hs k).2)
    _ = _ := by
      have h := Finset.sum_range_sub' (fun k : ℕ => (k + 1 : ℝ) ^ (-s)) n
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
        Real.one_rpow, add_assoc, one_add_one_eq_two] using h

theorem powerSumDiscrepancy_summable {s : ℝ} (hs : 0 ≤ s) :
    Summable (powerSumDiscrepancy s) := by
  apply summable_of_sum_range_le (c := 1)
    (fun n => (powerSumDiscrepancy_bounds hs n).1)
  intro n
  exact (powerSumDiscrepancy_sum_le hs n).trans (sub_le_self _ (by positivity))

lemma powerSumDiscrepancy_tsum_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ ∑' n, powerSumDiscrepancy s n ∧ ∑' n, powerSumDiscrepancy s n ≤ 1 := by
  refine ⟨tsum_nonneg (fun n => (powerSumDiscrepancy_bounds hs n).1), ?_⟩
  exact (powerSumDiscrepancy_summable hs).tsum_le_of_sum_range_le
    (fun n => (powerSumDiscrepancy_sum_le hs n).trans (sub_le_self _ (by positivity)))

lemma powerSumDiscrepancy_sum_eq (s : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, powerSumDiscrepancy s k =
      (∑ k ∈ Finset.range n, (k + 1 : ℝ) ^ (-s)) -
        ∫ x : ℝ in 1..(n + 1), x ^ (-s) := by
  unfold powerSumDiscrepancy
  rw [Finset.sum_sub_distrib]
  congr 1
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) + 1) (n := n) (f := fun x : ℝ => x ^ (-s)) (μ := volume)
    (fun k _ => intervalIntegral.intervalIntegrable_rpow (Or.inr
      (notMem_uIcc_of_lt (by positivity) (by positivity))))
  simpa only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one, add_assoc,
    one_add_one_eq_two] using h

theorem powerSumDiscrepancy_tail_bounds {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ (∑' k, powerSumDiscrepancy s k) -
        (∑ k ∈ Finset.range n, powerSumDiscrepancy s k) ∧
      (∑' k, powerSumDiscrepancy s k) -
        (∑ k ∈ Finset.range n, powerSumDiscrepancy s k) ≤ (n + 1 : ℝ) ^ (-s) := by
  have hsum := powerSumDiscrepancy_summable hs
  have heq := hsum.sum_add_tsum_nat_add n
  rw [← heq, add_sub_cancel_left]
  refine ⟨tsum_nonneg (fun k => (powerSumDiscrepancy_bounds hs (k + n)).1), ?_⟩
  apply ((summable_nat_add_iff n).mpr hsum).tsum_le_of_sum_range_le
  intro m
  calc
    _ ≤ ∑ k ∈ Finset.range m,
        (((k + n : ℕ) + 1 : ℝ) ^ (-s) - ((k + n : ℕ) + 2 : ℝ) ^ (-s)) :=
      Finset.sum_le_sum (fun k _ => (powerSumDiscrepancy_bounds hs (k + n)).2)
    _ = (n + 1 : ℝ) ^ (-s) - ((m + n : ℕ) + 1 : ℝ) ^ (-s) := by
      have h := Finset.sum_range_sub' (fun k : ℕ => ((k + n : ℕ) + 1 : ℝ) ^ (-s)) m
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
        add_assoc, add_left_comm (1 : ℝ), one_add_one_eq_two] using h
    _ ≤ _ := sub_le_self _ (by positivity)

noncomputable def realZetaRegularized (s : ℝ) : ℝ :=
  1 / (s - 1) + ∑' n, powerSumDiscrepancy s n

theorem realZetaRegularized_neg {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    realZetaRegularized s < 0 := by
  have h := (powerSumDiscrepancy_tsum_bounds hs.le).2
  unfold realZetaRegularized
  have hdiv : 1 / (s - 1) < -1 := by
    apply (div_lt_iff_of_neg (by linarith : s - 1 < 0)).mpr
    linarith
  linarith

theorem power_sum_regularized_error_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (n : ℕ) :
    |(∑ k ∈ Finset.range n, (k + 1 : ℝ) ^ (-s)) -
        (realZetaRegularized s + (n + 1 : ℝ) ^ (1 - s) / (1 - s))| ≤
      (n + 1 : ℝ) ^ (-s) := by
  have hi : (∫ x : ℝ in 1..(n + 1), x ^ (-s)) =
      ((n + 1 : ℝ) ^ (1 - s) - 1) / (1 - s) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -s)), Real.one_rpow]
    rw [show -s + 1 = 1 - s by ring]
  have hsum := powerSumDiscrepancy_sum_eq s n
  rw [hi] at hsum
  have htail := powerSumDiscrepancy_tail_bounds hs.le n
  have heq : (∑ k ∈ Finset.range n, (k + 1 : ℝ) ^ (-s)) -
      (realZetaRegularized s + (n + 1 : ℝ) ^ (1 - s) / (1 - s)) =
      -((∑' k, powerSumDiscrepancy s k) -
        (∑ k ∈ Finset.range n, powerSumDiscrepancy s k)) := by
    unfold realZetaRegularized
    rw [hsum]
    have hne : 1 - s ≠ 0 := by linarith
    have hneg : s - 1 = -(1 - s) := by ring
    rw [hneg, div_neg]
    field_simp
    ring
  rw [heq, abs_neg, abs_of_nonneg htail.1]
  exact htail.2

end Erdos1148.DukeArithmetic
