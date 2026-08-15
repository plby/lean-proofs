import Mathlib.Algebra.Group.Even
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem 888: foundational definitions

This file contains the statement layer for Erdős Problem 888 and the
elementary finite-maximum facts needed to use its extremal function.

The definitions `RequiredCondition` and `p` agree with the statement in the
Formal Conjectures repository.  We name the `Nat.findGreatest` expression
`extremalSize` so that later files can work with its specification rather
than unfolding a bounded search.
-/

open Filter

namespace Erdos888

/-- A set admissible for Erdős Problem 888 at parameter `n`.

Thus `A ⊆ {1, …, n}`, and every ordered quadruple from `A` whose product is
a square satisfies the required multiplicative equality. -/
def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
    a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

/-- There is an admissible set of cardinality `k` at parameter `n`. -/
def p (n : ℕ) (k : ℕ) : Prop :=
  ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

/-- The largest cardinality of an admissible set in `{1, …, n}`. -/
noncomputable def extremalSize (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (p n) n

open scoped Classical in
/-- Unfolding bridge to the `Nat.findGreatest` expression used verbatim in
the upstream Formal Conjectures statement. -/
theorem extremalSize_eq_findGreatest (n : ℕ) :
    extremalSize n = Nat.findGreatest (p n) n := by
  rfl

/-- The empty set is admissible for every parameter. -/
theorem requiredCondition_empty (n : ℕ) :
    RequiredCondition (∅ : Finset ℕ) n := by
  simp [RequiredCondition]

/-- Cardinality zero is always attained.  This supplies the base witness for
`Nat.findGreatest_spec`. -/
theorem p_zero (n : ℕ) : p n 0 :=
  ⟨∅, requiredCondition_empty n, by simp⟩

/-- Every admissible set has at most `n` elements. -/
theorem requiredCondition_card_le {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) : A.card ≤ n := by
  have hcard := Finset.card_le_card hA.1
  simpa using hcard

/-- Every cardinality represented by `p n` lies in the search interval
`[0, n]`. -/
theorem p_le {n k : ℕ} (hk : p n k) : k ≤ n := by
  obtain ⟨A, hA, rfl⟩ := hk
  exact requiredCondition_card_le hA

/-- The bounded maximum is at most its ambient parameter. -/
theorem extremalSize_le (n : ℕ) : extremalSize n ≤ n := by
  classical
  unfold extremalSize
  exact Nat.findGreatest_le n

/-- The maximum cardinality is attained. -/
theorem p_extremalSize (n : ℕ) : p n (extremalSize n) := by
  classical
  unfold extremalSize
  exact Nat.findGreatest_spec (P := p n) (m := 0)
    (Nat.zero_le n) (p_zero n)

/-- Any attainable cardinality is at most the extremal size. -/
theorem le_extremalSize_of_p {n k : ℕ} (hk : p n k) :
    k ≤ extremalSize n := by
  classical
  unfold extremalSize
  exact Nat.le_findGreatest (P := p n) (p_le hk) hk

/-- Every admissible set has cardinality at most the extremal size. -/
theorem card_le_extremalSize {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) : A.card ≤ extremalSize n :=
  le_extremalSize_of_p ⟨A, hA, rfl⟩

/-- An admissible extremizer exists for every `n`. -/
theorem exists_extremizer (n : ℕ) :
    ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = extremalSize n :=
  p_extremalSize n

/-- The scale appearing in the resolved asymptotic form of Erdős Problem
888. -/
noncomputable def scale (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (Real.log n) / Real.log n

/-- Eventually the Erdős 888 comparison scale is strictly positive. -/
theorem eventually_scale_pos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
  filter_upwards
    [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ)),
      (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))]
    with n hn hlog hloglog
  exact div_pos (mul_pos hn hloglog) hlog

/-- In particular, the Erdős 888 comparison scale is eventually nonzero. -/
theorem eventually_scale_ne_zero : ∀ᶠ n : ℕ in atTop, scale n ≠ 0 :=
  eventually_scale_pos.mono fun _ hn => ne_of_gt hn

end Erdos888
