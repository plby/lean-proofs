import ErdosProblems.Erdos380.Core
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Finite second-moment estimates

These inequalities apply to the actual uniform tuple space used in the
prime-product argument. They require neither independence nor a measure
theoretic probability-space replacement.
-/

open scoped BigOperators

namespace Erdos380

lemma expect_centered_square {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (f : Ω → ℝ) (μ : ℝ) :
    (𝔼 ω ∈ s, (f ω - μ) ^ 2) =
      (𝔼 ω ∈ s, f ω ^ 2) - 2 * μ * (𝔼 ω ∈ s, f ω) + μ ^ 2 := by
  calc
    _ = 𝔼 ω ∈ s, (f ω ^ 2 - (2 * μ) * f ω + μ ^ 2) := by
      apply Finset.expect_congr rfl
      intro ω _hω
      ring
    _ = _ := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        ← Finset.mul_expect, Finset.expect_const hs]

lemma expect_square_sum {ι Ω : Type*} (I : Finset ι) (s : Finset Ω) (f : ι → Ω → ℝ) :
    (𝔼 ω ∈ s, (∑ i ∈ I, f i ω) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, 𝔼 ω ∈ s, f i ω * f j ω := by
  simp_rw [pow_two, Finset.sum_mul_sum, Finset.expect_sum_comm]

/-- A second-moment bound with errors in both the first and second moments. -/
theorem finite_centered_second_moment_le {ι Ω : Type*}
    (I : Finset ι) (s : Finset Ω) (hs : s.Nonempty) (f : ι → Ω → ℝ)
    (a d : ι → ℝ) (e : ι → ι → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i)
    (hfirst : ∀ i ∈ I, a i - d i ≤ 𝔼 ω ∈ s, f i ω)
    (hpair : ∀ i ∈ I, ∀ j ∈ I,
      (𝔼 ω ∈ s, f i ω * f j ω) ≤ a i * a j + e i j) :
    (𝔼 ω ∈ s, ((∑ i ∈ I, f i ω) - ∑ i ∈ I, a i) ^ 2) ≤
      (∑ i ∈ I, ∑ j ∈ I, e i j) + 2 * (∑ i ∈ I, a i) * (∑ i ∈ I, d i) := by
  have hμ : 0 ≤ ∑ i ∈ I, a i := Finset.sum_nonneg ha
  have hfirstSum : (∑ i ∈ I, a i) - (∑ i ∈ I, d i) ≤
      𝔼 ω ∈ s, ∑ i ∈ I, f i ω := by
    rw [Finset.expect_sum_comm, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum hfirst
  have hsecondSum : (𝔼 ω ∈ s, (∑ i ∈ I, f i ω) ^ 2) ≤
      (∑ i ∈ I, a i) ^ 2 + (∑ i ∈ I, ∑ j ∈ I, e i j) := by
    rw [expect_square_sum]
    calc
      _ ≤ ∑ i ∈ I, ∑ j ∈ I, (a i * a j + e i j) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  rw [expect_centered_square s hs]
  have hmul := mul_le_mul_of_nonneg_left hfirstSum (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hμ)
  nlinarith

/-- Chebyshev's inequality on a finite uniform sample, with explicit cardinalities. -/
theorem finite_chebyshev {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) (μ t : ℝ) (ht : 0 < t) :
    ((s.filter fun ω => t ≤ |f ω - μ|).card : ℝ) / (s.card : ℝ) ≤
      (𝔼 ω ∈ s, (f ω - μ) ^ 2) / t ^ 2 := by
  classical
  have hcount : ((s.filter fun ω => t ≤ |f ω - μ|).card : ℝ) * t ^ 2 ≤
      ∑ ω ∈ s, (f ω - μ) ^ 2 := by
    calc
      _ = ∑ _ω ∈ s.filter (fun ω => t ≤ |f ω - μ|), t ^ 2 := by simp
      _ ≤ ∑ ω ∈ s.filter (fun ω => t ≤ |f ω - μ|), (f ω - μ) ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        have habs := (Finset.mem_filter.mp hω).2
        nlinarith [sq_abs (f ω - μ)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω _ _ => sq_nonneg (f ω - μ))
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  rw [Finset.expect_eq_sum_div_card]
  have hdiv := div_le_div_of_nonneg_right hcount (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)
  convert hdiv using 1 <;> ring

end Erdos380
