import Mathlib

/-! # A uniform finite subdivision of a dyadic real interval -/

namespace Erdos421

open MeasureTheory

noncomputable def windowGrid (X : ℝ) (N j : ℕ) : ℝ := X + (j : ℝ) * X / N

theorem windowGrid_zero (X : ℝ) (N : ℕ) : windowGrid X N 0 = X := by simp [windowGrid]

theorem windowGrid_end (X : ℝ) {N : ℕ} (hN : 0 < N) : windowGrid X N N = 2 * X := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold windowGrid
  field_simp
  ring

theorem windowGrid_step (X : ℝ) (N j : ℕ) :
    windowGrid X N (j + 1) - windowGrid X N j = X / N := by
  simp only [windowGrid, Nat.cast_add, Nat.cast_one]
  ring

theorem windowGrid_bounds {X : ℝ} (hX : 0 ≤ X) {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    X ≤ windowGrid X N j ∧ windowGrid X N j ≤ 2 * X := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjr : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold windowGrid
  constructor
  · have hp : 0 ≤ (j : ℝ) * X / N := by positivity
    linarith
  · have hb : (j : ℝ) * X / N ≤ X := by
      apply (div_le_iff₀ hNr).mpr
      nlinarith
    linarith

theorem windowGrid_step_properties {X : ℝ} (hX : 0 < X) {N j : ℕ} (hN : 0 < N)
    (hj : j < N) :
    0 < windowGrid X N j ∧ windowGrid X N j ≤ windowGrid X N (j + 1) ∧
      windowGrid X N (j + 1) ≤ (1 + (N : ℝ)⁻¹) * windowGrid X N j ∧
        windowGrid X N (j + 1) - windowGrid X N j ≤ X := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase := windowGrid_bounds hX.le hN hj.le
  have hstep := windowGrid_step X N j
  have hsmall : X / N ≤ X := div_le_self hX.le hN1
  have hratio : X / N ≤ (N : ℝ)⁻¹ * windowGrid X N j := by
    have h := div_le_div_of_nonneg_right hbase.1 hNr.le
    simpa only [div_eq_mul_inv, mul_comm] using h
  refine ⟨hX.trans_le hbase.1, ?_, ?_, ?_⟩
  · have hpos := div_nonneg hX.le hNr.le
    linarith
  · nlinarith
  · linarith

theorem windowGrid_integral_bound (f : ℝ → ℝ) {X : ℝ} (hX : 0 < X)
    {N : ℕ} (hN : 0 < N) (hf : ContinuousOn f (Set.Icc X (2 * X))) {U V : ℝ}
    (hbound : ∀ j < N, (∫ x in windowGrid X N j..windowGrid X N (j + 1), f x) ≤
      (windowGrid X N (j + 1) - windowGrid X N j) * U + V) :
    (∫ x in X..2 * X, f x) ≤ X * U + N * V := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hI (j : ℕ) (hj : j < N) :
      IntervalIntegrable f volume (windowGrid X N j) (windowGrid X N (j + 1)) := by
    have hleft := (windowGrid_bounds hX.le hN hj.le).1
    have hright := (windowGrid_bounds hX.le hN (by omega : j + 1 ≤ N)).2
    exact (hf.mono (fun x hx ↦ ⟨hleft.trans hx.1, hx.2.trans hright⟩)).intervalIntegrable_of_Icc
      (windowGrid_step_properties hX hN hj).2.1
  have he := intervalIntegral.sum_integral_adjacent_intervals hI
  rw [windowGrid_zero, windowGrid_end _ hN] at he
  rw [← he]
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ((windowGrid X N (j + 1) - windowGrid X N j) * U + V) :=
      Finset.sum_le_sum (fun j hj ↦ hbound j (Finset.mem_range.mp hj))
    _ = (N : ℝ) * (X / N * U + V) := by simp only [windowGrid_step, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    _ = _ := by field_simp

end Erdos421
