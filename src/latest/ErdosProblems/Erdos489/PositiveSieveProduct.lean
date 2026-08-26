import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators

/-- A summable sequence of numbers in `[0,1)` has finite products
`∏_{n<N}(1-x_n)` eventually bounded below by a fixed positive constant. -/
theorem eventually_pos_le_prod_one_sub_of_summable
    (x : ℕ → ℝ) (hs : Summable x)
    (hx0 : ∀ n, 0 ≤ x n) (hx1 : ∀ n, x n < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ N : ℕ in atTop, ρ ≤ ∏ n ∈ Finset.range N, (1 - x n) := by
  let f : ℕ → ℝ := fun n => -x n
  have hnorm : Summable (fun n => ‖f n‖) := by
    have h := hs.norm
    apply h.congr
    intro n
    simp only [f, norm_neg, Real.norm_eq_abs, abs_of_nonneg (hx0 n)]
  have hmult : Multipliable (fun n => 1 + f n) :=
    multipliable_one_add_of_summable hnorm
  have hne : ∀ n, 1 + f n ≠ 0 := by
    intro n
    dsimp [f]
    linarith [hx1 n]
  have htne : (∏' n : ℕ, (1 + f n)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hne hnorm
  have htend : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + f n))
      atTop (𝓝 (∏' n : ℕ, (1 + f n))) :=
    hmult.hasProd.tendsto_prod_nat
  have hprod0 : ∀ N, 0 ≤ ∏ n ∈ Finset.range N, (1 + f n) := by
    intro N
    apply Finset.prod_nonneg
    intro n hn
    dsimp [f]
    linarith [hx1 n]
  have ht0 : 0 ≤ ∏' n : ℕ, (1 + f n) :=
    ge_of_tendsto htend (Filter.Eventually.of_forall hprod0)
  have htpos : 0 < ∏' n : ℕ, (1 + f n) := lt_of_le_of_ne ht0 (Ne.symm htne)
  let ρ : ℝ := (∏' n : ℕ, (1 + f n)) / 2
  refine ⟨ρ, by dsimp [ρ]; positivity, ?_⟩
  have hρlt : ρ < ∏' n : ℕ, (1 + f n) := by
    dsimp [ρ]
    linarith
  have hev : ∀ᶠ N : ℕ in atTop,
      ρ < ∏ n ∈ Finset.range N, (1 + f n) :=
    (tendsto_order.1 htend).1 ρ hρlt
  filter_upwards [hev] with N hN
  have heq : (∏ n ∈ Finset.range N, (1 + f n)) =
      ∏ n ∈ Finset.range N, (1 - x n) := by
    apply Finset.prod_congr rfl
    intro n hn
    simp [f, sub_eq_add_neg]
  rw [← heq]
  exact hN.le

/-- Reciprocal specialization used for divisor sieves. -/
theorem eventually_pos_le_reciprocal_sieve_product
    (a : ℕ → ℕ) (ha2 : ∀ n, 2 ≤ a n)
    (hs : Summable fun n => ((a n : ℝ)⁻¹)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ N : ℕ in atTop,
        ρ ≤ ∏ n ∈ Finset.range N, (1 - (a n : ℝ)⁻¹) := by
  apply eventually_pos_le_prod_one_sub_of_summable
    (fun n => ((a n : ℝ)⁻¹)) hs
  · intro n
    positivity
  · intro n
    have ha : (1 : ℝ) < a n := by exact_mod_cast ha2 n
    exact inv_lt_one_of_one_lt₀ ha

end Erdos489
