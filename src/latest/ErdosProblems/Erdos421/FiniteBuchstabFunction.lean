import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Finite iterates of Buchstab's integral equation

Only bounded arguments are needed for the chosen prime cutoff. Each iterate is
defined on the whole real line using harmless clamping below the relevant range;
the stability theorem proves exact agreement on the required successive ranges.
-/

namespace Erdos421

open MeasureTheory

noncomputable def finiteBuchstab : ℕ → ℝ → ℝ
  | 0, u => 1 / max 1 u
  | n + 1, u => (1 + ∫ t in (2 : ℝ)..max 2 u, finiteBuchstab n (t - 1)) / max 1 u

theorem finiteBuchstab_continuous (n : ℕ) : Continuous (finiteBuchstab n) := by
  induction n with
  | zero =>
    exact continuous_const.div (continuous_const.max continuous_id)
      (fun u ↦ (lt_of_lt_of_le zero_lt_one (le_max_left 1 u)).ne')
  | succ n ih =>
    have hc : Continuous (fun t : ℝ ↦ finiteBuchstab n (t - 1)) :=
      ih.comp (continuous_id.sub continuous_const)
    have hi : Continuous (fun u : ℝ ↦ ∫ t in (2 : ℝ)..u, finiteBuchstab n (t - 1)) :=
      intervalIntegral.continuous_primitive (fun a b ↦ hc.intervalIntegrable a b) 2
    exact (continuous_const.add (hi.comp (continuous_const.max continuous_id))).div
      (continuous_const.max continuous_id)
      (fun u ↦ (lt_of_lt_of_le zero_lt_one (le_max_left 1 u)).ne')

theorem finiteBuchstab_pos (n : ℕ) (u : ℝ) : 0 < finiteBuchstab n u := by
  induction n generalizing u with
  | zero => exact div_pos zero_lt_one (lt_of_lt_of_le zero_lt_one (le_max_left 1 u))
  | succ n ih =>
    have hi : 0 ≤ ∫ t in (2 : ℝ)..max 2 u, finiteBuchstab n (t - 1) :=
      intervalIntegral.integral_nonneg_of_forall (le_max_left 2 u)
        (fun t ↦ (ih (t - 1)).le)
    exact div_pos (by linarith : 0 < 1 + ∫ t in (2 : ℝ)..max 2 u,
      finiteBuchstab n (t - 1)) (lt_of_lt_of_le zero_lt_one (le_max_left 1 u))

theorem finiteBuchstab_of_le_two (n : ℕ) {u : ℝ} (hu : u ≤ 2) :
    finiteBuchstab n u = 1 / max 1 u := by
  cases n <;> simp only [finiteBuchstab, max_eq_left hu, intervalIntegral.integral_same, add_zero]

theorem finiteBuchstab_initial (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    finiteBuchstab n u = 1 / u := by
  rw [finiteBuchstab_of_le_two n hu.2, max_eq_right hu.1]

theorem finiteBuchstab_step (n : ℕ) {u : ℝ} (hu : 2 ≤ u) :
    finiteBuchstab (n + 1) u = (1 + ∫ t in (2 : ℝ)..u, finiteBuchstab n (t - 1)) / u := by
  rw [finiteBuchstab, max_eq_right hu, max_eq_right (show 1 ≤ u by linarith)]

theorem finiteBuchstab_stable (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 2) :
    finiteBuchstab (n + 1) u = finiteBuchstab n u := by
  induction n generalizing u with
  | zero =>
    rw [finiteBuchstab_of_le_two 1 (by simpa using hu), finiteBuchstab]
  | succ n ih =>
    norm_num only [Nat.cast_add, Nat.cast_one] at hu
    have hu' : u ≤ (n : ℝ) + 3 := by linarith
    change (1 + ∫ t in (2 : ℝ)..max 2 u, finiteBuchstab (n + 1) (t - 1)) / max 1 u =
      (1 + ∫ t in (2 : ℝ)..max 2 u, finiteBuchstab n (t - 1)) / max 1 u
    congr 2
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (le_max_left 2 u)] at ht
    apply ih
    have hm : max 2 u ≤ (n : ℝ) + 3 :=
      max_le (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) hu'
    linarith [ht.2]

end Erdos421
