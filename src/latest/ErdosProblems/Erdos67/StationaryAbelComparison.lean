import ErdosProblems.Erdos67.StationaryPrimeErrorLower
import Mathlib.Algebra.BigOperators.Module

/-! # Positive summation-by-parts comparison -/

open scoped BigOperators Topology
open Finset Filter

namespace Erdos67.StationaryModel

theorem weighted_sum_le_of_prefix_le (a b w : ℕ → ℝ) (D : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hmono : Antitone w)
    (hprefix : ∀ N, (∑ n ∈ range N, a n) ≤ (∑ n ∈ range N, b n) + D)
    (N : ℕ) :
    (∑ n ∈ range (N + 1), w n * a n) ≤
      (∑ n ∈ range (N + 1), w n * b n) + D * w 0 := by
  have ha := sum_range_by_parts w a (N + 1)
  have hb := sum_range_by_parts w b (N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at ha hb
  have ht : (∑ n ∈ range N, (w n - w (n + 1))) = w 0 - w N := by
    clear ha hb
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hmain := mul_le_mul_of_nonneg_left (hprefix (N + 1)) (hw N)
  have hsum : (∑ n ∈ range N, (w n - w (n + 1)) * ∑ i ∈ range (n + 1), a i) ≤
      ∑ n ∈ range N, (w n - w (n + 1)) * ((∑ i ∈ range (n + 1), b i) + D) := by
    apply sum_le_sum
    intro n _
    exact mul_le_mul_of_nonneg_left (hprefix (n + 1))
      (sub_nonneg.mpr (hmono (Nat.le_succ n)))
  have hneg (f : ℕ → ℝ) :
      -(∑ n ∈ range N, (w (n + 1) - w n) * ∑ i ∈ range (n + 1), f i) =
      ∑ n ∈ range N, (w n - w (n + 1)) * ∑ i ∈ range (n + 1), f i := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [ha, hb, sub_eq_add_neg, sub_eq_add_neg, hneg a, hneg b]
  simp only [mul_add, sum_add_distrib, ← sum_mul, ht] at hsum
  nlinarith only [hmain, hsum]

theorem summable_harmonic_of_eventual_prefix_le (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hprefix : ∀ᶠ N : ℕ in atTop, (∑ n ∈ range N, a n) ≤ ∑ n ∈ range N, b n)
    (hsum : Summable (fun n ↦ b n / (n + 1 : ℕ))) :
    Summable (fun n ↦ a n / (n + 1 : ℕ)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hprefix
  let D := ∑ n ∈ range K, a n
  have hD : 0 ≤ D := sum_nonneg fun n _ ↦ ha n
  have hall (N : ℕ) : (∑ n ∈ range N, a n) ≤ (∑ n ∈ range N, b n) + D := by
    by_cases hKN : K ≤ N
    · exact (hK N hKN).trans (le_add_of_nonneg_right hD)
    · have hs : (∑ n ∈ range N, a n) ≤ D :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun n _ _ ↦ ha n)
      exact hs.trans (le_add_of_nonneg_left (sum_nonneg fun n _ ↦ hb n))
  apply summable_of_sum_range_le (fun n ↦ div_nonneg (ha n) (Nat.cast_nonneg _))
    (c := (∑' n, b n / (n + 1 : ℕ)) + D)
  intro N
  cases N with
  | zero =>
    rw [sum_range_zero]
    exact add_nonneg (tsum_nonneg fun n ↦ div_nonneg (hb n) (Nat.cast_nonneg (n + 1))) hD
  | succ N =>
    have hh := weighted_sum_le_of_prefix_le a b (fun n ↦ 1 / (n + 1 : ℕ)) D
      (fun n ↦ by positivity) (fun m n hmn ↦ one_div_le_one_div_of_le
        (Nat.cast_pos.mpr (Nat.succ_pos m)) (by exact_mod_cast Nat.succ_le_succ hmn)) hall N
    simp only [one_div, inv_mul_eq_div, Nat.zero_add, Nat.cast_one, inv_one, mul_one] at hh
    apply hh.trans
    gcongr
    exact hsum.sum_le_tsum (range (N + 1))
      (fun n _ ↦ div_nonneg (hb n) (Nat.cast_nonneg _))

end Erdos67.StationaryModel
