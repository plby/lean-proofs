import ErdosProblems.Erdos489.UniformGapTail
import ErdosProblems.Erdos489.TruncatedGapApproximation

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators

namespace Erdos489

/-- The normalized full squared-gap sum for the infinite divisor sieve. -/
noncomputable def fullGapAverage (p : ℕ → Prop) (x : ℕ) : ℝ :=
  ((∑ i ∈ Finset.range (Nat.count (divisorSifted p) x),
      (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ)

/-- Exact decomposition into short-gap local cost and the long-gap tail. -/
theorem fullGapAverage_eq_truncated_add_tail
    (p : ℕ → Prop) [DecidablePred p]
    (hB : Set.Infinite {n | divisorSifted p n}) (H x : ℕ) :
    fullGapAverage p x = fullTruncatedGapAverage p H x +
      (((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ)) := by
  classical
  have hshort := sum_truncatedGapCost_eq_gap_sum
    (divisorSifted p) hB H x
  have hpart := Finset.sum_filter_add_sum_filter_not
    (Finset.range (Nat.count (divisorSifted p) x))
    (fun i => divisorSiftedGap p i < H)
    (fun i => (divisorSiftedGap p i) ^ 2)
  simp only [not_lt] at hpart
  have htotal :
      (∑ i ∈ Finset.range (Nat.count (divisorSifted p) x),
        (divisorSiftedGap p i) ^ 2) =
      (∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n) +
      (∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
        (fun i => H ≤ divisorSiftedGap p i),
        (divisorSiftedGap p i) ^ 2) := by
    have hs : (∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n) =
      ∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
        (fun i => divisorSiftedGap p i < H),
        (divisorSiftedGap p i) ^ 2 := by
      simpa [divisorSiftedGap, divisorSiftedEnumeration] using hshort
    omega
  unfold fullGapAverage fullTruncatedGapAverage
  rw [htotal]
  norm_num only [Nat.cast_add]
  ring

/-- The normalized full squared-gap sum converges for every infinite forbidden
predicate satisfying the established thinness consequences. -/
theorem exists_fullGapAverage_limit
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (hB : Set.Infinite {n | divisorSifted p n})
    (hs : Summable fun n => ((Nat.nth p n : ℝ)⁻¹))
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    ∃ L : ℝ, Tendsto (fullGapAverage p) atTop (𝓝 L) := by
  apply exists_tendsto_of_uniform_eventual_approx
    (fullGapAverage p) (fun H => fullTruncatedGapAverage p H)
  · intro ε hε
    obtain ⟨H, htail⟩ := uniform_long_gap_square_tail
      p hp hp2 hB hs hev hcount ε hε
    refine ⟨H, ?_⟩
    filter_upwards [htail] with x hx
    rw [fullGapAverage_eq_truncated_add_tail p hB H x,
      add_sub_cancel_left]
    rw [abs_of_nonneg (by positivity)]
    exact hx
  · intro H
    exact exists_fullTruncatedGapAverage_limit p hp hp2 hcount hs H

end Erdos489
