import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat

/-!
# Weighted Cauchy and grouping by residue classes

This file records two elementary finite identities used when passing from a
logarithmically weighted average to the residue-class sums in Tao's Section 4.
They are deliberately independent of the analytic estimates in the rest of
the Erdős discrepancy development.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

/-- Finite weighted Cauchy--Schwarz for complex-valued data. -/
theorem normSq_weighted_sum_le_mul_weighted_normSq {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (F : ι → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    Complex.normSq (∑ i ∈ s, (w i : ℂ) * F i) ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * Complex.normSq (F i) := by
  classical
  have hcauchy :
      (∑ i ∈ s, w i * norm (F i)) ^ 2 ≤
        (∑ i ∈ s, w i) * ∑ i ∈ s, w i * norm (F i) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    · exact hw
    · intro i hi
      exact mul_nonneg (hw i hi) (sq_nonneg _)
    · intro i hi
      convert le_refl (w i ^ 2 * norm (F i) ^ 2) using 1 <;> ring
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ i ∈ s, (w i : ℂ) * F i‖ ^ 2 ≤
        (∑ i ∈ s, norm ((w i : ℂ) * F i)) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ = (∑ i ∈ s, w i * norm (F i)) ^ 2 := by
      apply congrArg (fun x : ℝ ↦ x ^ 2)
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw i hi)]
    _ ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * norm (F i) ^ 2 := hcauchy
    _ = (∑ x ∈ s, w x) *
          ∑ x ∈ s, w x * Complex.normSq (F x) := by
      simp only [Complex.normSq_eq_norm_sq]

/-- The elements of `s` lying in the residue class of `a` modulo `r`.  Using
`a % r` makes the definition insensitive to the chosen representative. -/
def residueFiber (s : Finset ℕ) (r a : ℕ) : Finset ℕ :=
  s.filter fun n ↦ n % r = a % r

@[simp] theorem mem_residueFiber {s : Finset ℕ} {r a n : ℕ} :
    n ∈ residueFiber s r a ↔ n ∈ s ∧ n % r = a % r := by
  simp [residueFiber]

/-- Group a finite weighted local sum by a residue class and replace a
periodic coefficient by its value at the chosen representative.  The
hypothesis relates the two coefficient functions pointwise on congruent
integers; in applications `uResidue` is the periodic character model. -/
theorem weighted_local_sum_residue_grouping
    (s : Finset ℕ) (r a L : ℕ) (w : ℕ → ℝ)
    (u uResidue h : ℕ → ℂ)
    (hperiodic : ∀ x y : ℕ, x % r = y % r → u x = uResidue y) :
    (∑ n ∈ residueFiber s r a,
        (w n : ℂ) * ∑ m ∈ Finset.Icc 1 L, u (n + m) * h (n + m)) =
      ∑ m ∈ Finset.Icc 1 L, uResidue (a + m) *
        ∑ n ∈ residueFiber s r a, (w n : ℂ) * h (n + m) := by
  classical
  calc
    (∑ n ∈ residueFiber s r a,
        (w n : ℂ) * ∑ m ∈ Finset.Icc 1 L, u (n + m) * h (n + m)) =
        ∑ n ∈ residueFiber s r a, ∑ m ∈ Finset.Icc 1 L,
          (w n : ℂ) * (u (n + m) * h (n + m)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 L, ∑ n ∈ residueFiber s r a,
          (w n : ℂ) * (u (n + m) * h (n + m)) := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.Icc 1 L, uResidue (a + m) *
          ∑ n ∈ residueFiber s r a, (w n : ℂ) * h (n + m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hna : n % r = a % r := (mem_residueFiber.mp hn).2
      have hnam : (n + m) % r = (a + m) % r :=
        (show n ≡ a [MOD r] from hna).add_right m
      rw [hperiodic (n + m) (a + m) hnam]
      ring

/-- Localized form of `weighted_local_sum_residue_grouping`.  This is the
form used for modified characters, whose periodicity holds only on the good
shifted residue classes under consideration. -/
theorem weighted_local_sum_residue_grouping_of_fiber
    (s : Finset ℕ) (r a L : ℕ) (w : ℕ → ℝ)
    (u uResidue h : ℕ → ℂ)
    (hperiodic : ∀ n ∈ residueFiber s r a, ∀ m ∈ Finset.Icc 1 L,
      u (n + m) = uResidue (a + m)) :
    (∑ n ∈ residueFiber s r a,
        (w n : ℂ) * ∑ m ∈ Finset.Icc 1 L, u (n + m) * h (n + m)) =
      ∑ m ∈ Finset.Icc 1 L, uResidue (a + m) *
        ∑ n ∈ residueFiber s r a, (w n : ℂ) * h (n + m) := by
  classical
  calc
    (∑ n ∈ residueFiber s r a,
        (w n : ℂ) * ∑ m ∈ Finset.Icc 1 L, u (n + m) * h (n + m)) =
        ∑ n ∈ residueFiber s r a, ∑ m ∈ Finset.Icc 1 L,
          (w n : ℂ) * (u (n + m) * h (n + m)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 L, ∑ n ∈ residueFiber s r a,
          (w n : ℂ) * (u (n + m) * h (n + m)) := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.Icc 1 L, uResidue (a + m) *
          ∑ n ∈ residueFiber s r a, (w n : ℂ) * h (n + m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [hperiodic n hn m hm]
      ring

end

end Erdos67b
