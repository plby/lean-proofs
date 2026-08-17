import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

/-!
# Finite analytic inequalities for Erdős problem 565

This file collects the elementary finite inequalities used by the container
and Janson parts of the induced-Ramsey argument.  In particular, all weighted
sums below are honest `Finset` sums; no measure-theoretic or asymptotic
machinery is hidden in the statements.
-/

open scoped BigOperators

namespace Erdos565
namespace FiniteAnalysis

/-- Weighted Cauchy--Schwarz, in a form that does not require taking square
roots of the weights. -/
theorem weighted_cauchy_schwarz
    {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i * g i) ^ 2 ≤
      (∑ i ∈ s, w i * f i ^ 2) * (∑ i ∈ s, w i * g i ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    ring_nf
    exact le_rfl

/-- Engel's form of finite Cauchy--Schwarz, arranged so that it can be
used directly with a positive mass `g i` in a denominator. -/
theorem sum_sq_le_sum_mul_sum_sq_div
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i) ^ 2 ≤
      (∑ i ∈ s, g i) * (∑ i ∈ s, f i ^ 2 / g i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := s) (r := f) (f := fun i ↦ f i ^ 2 / g i) (g := g)
    (fun i hi ↦ div_nonneg (sq_nonneg _) (hg i hi).le)
    (fun i hi ↦ (hg i hi).le)
    (fun i hi ↦ by rw [div_mul_cancel₀ (f i ^ 2) (hg i hi).ne'])
  simpa [mul_comm] using h

/-- Reciprocal-weight form of finite Cauchy--Schwarz. -/
theorem sum_sq_le_sum_mul_sum_sq_mul_inv
    {ι : Type*} (s : Finset ι) (f w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, f i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, f i ^ 2 * (w i)⁻¹) := by
  simpa [div_eq_mul_inv] using sum_sq_le_sum_mul_sum_sq_div s f w hw

/-- The one-function weighted Cauchy--Schwarz inequality. -/
theorem weighted_sum_sq_le
    {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i ^ 2) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (weighted_cauchy_schwarz s w f (fun _ ↦ (1 : ℝ)) hw)

/-- Division form of weighted Cauchy--Schwarz. -/
theorem weighted_sum_sq_div_le
    {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hwsum : 0 < ∑ i ∈ s, w i) :
    (∑ i ∈ s, w i * f i) ^ 2 / (∑ i ∈ s, w i) ≤
      ∑ i ∈ s, w i * f i ^ 2 := by
  rw [div_le_iff₀ hwsum]
  simpa [mul_comm] using weighted_sum_sq_le s w f hw

/-- Jensen's inequality for the square function and a finite family of
nonnegative weights of total mass one. -/
theorem sq_weighted_sum_le_of_sum_eq_one
    {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hwsum : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i * f i) ^ 2 ≤ ∑ i ∈ s, w i * f i ^ 2 := by
  simpa [hwsum] using weighted_sum_sq_le s w f hw

/-- The two-point instance of convexity of the square function. -/
theorem sq_convex_combination_le
    {a b t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (t * a + (1 - t) * b) ^ 2 ≤ t * a ^ 2 + (1 - t) * b ^ 2 := by
  nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr ht₁), sq_nonneg (a - b)]

/-- The sum of squares of nonnegative terms is at most the square of their
sum. -/
theorem sum_sq_le_sq_sum_of_nonneg
    {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i ^ 2) ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfsum : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hih := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      nlinarith

/-- Unweighted finite Cauchy--Schwarz, specialized to real-valued sums. -/
theorem sq_sum_le_card_mul_sum_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  simpa using (_root_.sq_sum_le_card_mul_sum_sq (s := s) (f := f))

/-- A partial row of Pascal's triangle is bounded by the whole row. -/
theorem partial_choose_sum_le_two_pow (n k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), n.choose i) ≤ 2 ^ n := by
  calc
    (∑ i ∈ Finset.range (k + 1), n.choose i) ≤
        ∑ i ∈ Finset.range (n + 1), n.choose i := by
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hk))
    _ = 2 ^ n := Nat.sum_range_choose n

/-- A deliberately coarse bound which is available without a relation
between the cutoff and the row number. -/
theorem partial_choose_sum_le_card_mul_two_pow (n k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), n.choose i) ≤ (k + 1) * 2 ^ n := by
  calc
    (∑ i ∈ Finset.range (k + 1), n.choose i) ≤
        ∑ _i ∈ Finset.range (k + 1), 2 ^ n := by
      exact Finset.sum_le_sum fun i _ ↦ Nat.choose_le_two_pow n i
    _ = (k + 1) * 2 ^ n := by simp

/-- Product form of the full-row bounds, useful when two fingerprints are
chosen independently. -/
theorem mul_partial_choose_sum_le_two_pow_add
    (n m k l : ℕ) (hk : k ≤ n) (hl : l ≤ m) :
    (∑ i ∈ Finset.range (k + 1), n.choose i) *
        (∑ j ∈ Finset.range (l + 1), m.choose j) ≤ 2 ^ (n + m) := by
  calc
    (∑ i ∈ Finset.range (k + 1), n.choose i) *
          (∑ j ∈ Finset.range (l + 1), m.choose j)
        ≤ 2 ^ n * 2 ^ m :=
      Nat.mul_le_mul (partial_choose_sum_le_two_pow n k hk)
        (partial_choose_sum_le_two_pow m l hl)
    _ = 2 ^ (n + m) := by rw [pow_add]

end FiniteAnalysis
end Erdos565
