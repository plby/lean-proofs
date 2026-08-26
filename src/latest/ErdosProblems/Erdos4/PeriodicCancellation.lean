import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

/-!
# Elementary cancellation of periodic sums

Only complete-period cancellation and a bound on individual terms are used.
This is the character-sum estimate needed for the weak prime-supported sieve.
-/

open scoped BigOperators

namespace Erdos4.PeriodicCancellation

theorem norm_sum_range_le_period (f : ℕ → ℂ) (d : ℕ) (hd : 0 < d)
    (hperiod : ∀ n, f (n + d) = f n)
    (hzero : ∑ n ∈ Finset.range d, f n = 0)
    (hbound : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f n‖ ≤ d := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hNd : N < d
    · calc
        ‖∑ n ∈ Finset.range N, f n‖ ≤ ∑ n ∈ Finset.range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun n _hn => hbound n)
        _ = N := by simp
        _ ≤ d := by exact_mod_cast hNd.le
    · have hle : d ≤ N := Nat.le_of_not_gt hNd
      have hsub : N - d < N := by omega
      have hsplit : (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range (N - d), f n := by
        calc
          (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range (d + (N - d)), f n := by
            rw [Nat.add_sub_of_le hle]
          _ = (∑ n ∈ Finset.range d, f n) + ∑ n ∈ Finset.range (N - d), f (d + n) :=
            Finset.sum_range_add f d (N - d)
          _ = ∑ n ∈ Finset.range (N - d), f n := by
            rw [hzero, zero_add]
            exact Finset.sum_congr rfl (fun n _hn => by simpa only [Nat.add_comm] using hperiod n)
      rw [hsplit]
      exact ih (N - d) hsub

theorem sum_shifted_period_eq_zero (f : ℕ → ℂ) (d : ℕ)
    (hperiod : ∀ n, f (n + d) = f n)
    (hzero : ∑ n ∈ Finset.range d, f n = 0) (a : ℕ) :
    ∑ n ∈ Finset.range d, f (a + n) = 0 := by
  induction a with
  | zero => simpa using hzero
  | succ a ih =>
    have h1 := Finset.sum_range_succ (fun n => f (a + n)) d
    have h2 := Finset.sum_range_succ' (fun n => f (a + n)) d
    have hedge : f (a + d) = f a := hperiod a
    have hshift : (∑ n ∈ Finset.range d, f (a + (n + 1))) =
        ∑ n ∈ Finset.range d, f (a + 1 + n) := by
      exact Finset.sum_congr rfl (fun n _hn => congrArg f (by omega))
    rw [hshift] at h2
    simp only [ih, zero_add, hedge] at h1
    have hsame := h1.symm.trans h2
    exact add_left_cancel (show f a + ∑ n ∈ Finset.range d, f (a + 1 + n) = f a + 0 by
      simpa only [add_comm, add_zero] using hsame.symm)

theorem norm_sum_interval_le_period (f : ℕ → ℂ) (d : ℕ) (hd : 0 < d)
    (hperiod : ∀ n, f (n + d) = f n)
    (hzero : ∑ n ∈ Finset.range d, f n = 0)
    (hbound : ∀ n, ‖f n‖ ≤ 1) (a N : ℕ) :
    ‖∑ n ∈ Finset.range N, f (a + n)‖ ≤ d := by
  apply norm_sum_range_le_period (fun n => f (a + n)) d hd
  · intro n
    simpa only [← Nat.add_assoc] using hperiod (a + n)
  · exact sum_shifted_period_eq_zero f d hperiod hzero a
  · intro n
    exact hbound (a + n)

theorem sum_range_zmod_eq {d : ℕ} [NeZero d] (f : ZMod d → ℂ) :
    (∑ n ∈ Finset.range d, f (n : ZMod d)) = ∑ a : ZMod d, f a := by
  classical
  apply Finset.sum_bij (fun (n : ℕ) (_hn : n ∈ Finset.range d) => (n : ZMod d))
  · intro n _hn
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using hv
  · intro a _ha
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro n _hn
    rfl

/-- The elementary interval bound for every nonprincipal Dirichlet character. -/
theorem character_norm_sum_interval_le {d : ℕ} [NeZero d]
    (chi : DirichletCharacter ℂ d) (hchi : chi ≠ 1) (a N : ℕ) :
    ‖∑ n ∈ Finset.range N, chi ((a + n : ℕ) : ZMod d)‖ ≤ d := by
  apply norm_sum_interval_le_period (fun n => chi (n : ZMod d)) d (NeZero.pos d)
  · intro n
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
  · rw [sum_range_zmod_eq]
    exact MulChar.sum_eq_zero_of_ne_one hchi
  · intro n
    exact chi.norm_le_one (n : ZMod d)

end Erdos4.PeriodicCancellation
