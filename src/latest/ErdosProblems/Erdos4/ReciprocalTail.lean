import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Uniform finite reciprocal-square tails

A single lower prime cutoff controls every finite collection of distinct
larger integers. Both reciprocal-square tails used by the coefficient
energy and projection comparison are covered.
-/

open scoped BigOperators

namespace Erdos4.ReciprocalTail

theorem exists_finite_tail_bound (f : ℕ → ℝ) (hf : Summable f) (hpos : ∀ n, 0 ≤ f n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ S : Finset ℕ, (∀ n ∈ S, K < n) → ∑ n ∈ S, f n < ε := by
  obtain ⟨S₀, hS₀⟩ := summable_iff_vanishing_norm.mp hf ε hε
  refine ⟨max 2 (S₀.sup id), le_max_left _ _, ?_⟩
  intro S hS
  have hd : Disjoint S S₀ := by
    apply Finset.disjoint_left.mpr
    intro n hn hn₀
    have hbound : n ≤ S₀.sup id := Finset.le_sup (f := id) hn₀
    have hgt := hS n hn
    have hmax := le_max_right 2 (S₀.sup id)
    omega
  have hh := hS₀ S hd
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun n _hn => hpos n))] using hh

theorem shifted_reciprocal_square_summable :
    Summable (fun n : ℕ => (((n : ℝ) - 1)⁻¹) ^ 2) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, inv_pow] using
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))

/-- The cutoff is independent of the finite upper endpoint. -/
theorem exists_reciprocal_square_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ S : Finset ℕ, (∀ n ∈ S, K < n) →
      (∑ n ∈ S, (((n : ℝ) - 1)⁻¹) ^ 2) < ε ∧
      (∑ n ∈ S, 1 / (n : ℝ) ^ 2) < ε := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_finite_tail_bound
    (fun n : ℕ => (((n : ℝ) - 1)⁻¹) ^ 2) shifted_reciprocal_square_summable
    (fun n => sq_nonneg _) hε
  obtain ⟨K₂, hK₂, h₂⟩ := exists_finite_tail_bound
    (fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    (fun n => div_nonneg zero_le_one (sq_nonneg _)) hε
  refine ⟨max K₁ K₂, hK₁.trans (le_max_left _ _), ?_⟩
  intro S hS
  exact ⟨h₁ S (fun n hn => lt_of_le_of_lt (le_max_left _ _) (hS n hn)),
    h₂ S (fun n hn => lt_of_le_of_lt (le_max_right _ _) (hS n hn))⟩

theorem indexed_sum_lt {P : Type*} [Fintype P]
    (f : ℕ → ℝ) {K : ℕ} {ε : ℝ}
    (hK : ∀ S : Finset ℕ, (∀ n ∈ S, K < n) → ∑ n ∈ S, f n < ε)
    (ell : P → ℕ) (hinj : Function.Injective ell) (hell : ∀ p, K < ell p) :
    (∑ p, f (ell p)) < ε := by
  classical
  rw [← Finset.sum_image (f := f) hinj.injOn]
  apply hK
  intro n hn
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hn
  exact hell p

end Erdos4.ReciprocalTail
