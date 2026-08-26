/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The finite positivity layer of Pinner's weighted Selberg argument

Pinner uses a nonnegative square weight and the score

`1 - ρ * ∑ i, τ (L i n)`.

For the deliberately non-optimal choice `ρ = 1 / 209`, positivity forces
the integral bound `∑ i, τ (L i n) ≤ 208`.  This file isolates that exact
finite implication from the analytic estimates for the two quadratic sums.
-/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.sigma
open Finset Nat ArithmeticFunction

namespace Erdos946.PinnerWeights

noncomputable section

/-- Pinner's polynomial Selberg coefficient, specialized to eight forms.
The exponent is `k + 1 = 9`. -/
def selbergCoefficient (xi d : ℕ) : ℝ :=
  if d ≤ xi then
    (μ d : ℝ) *
      (Real.log ((xi : ℝ) / d) / Real.log xi) ^ (9 : ℕ)
  else 0

/-- The square of the divisor sum occurring in Pinner's `Q₁` and `Q₂`. -/
def squareWeight (xi m : ℕ) : ℝ :=
  (∑ d ∈ m.divisors, selbergCoefficient xi d) ^ 2

lemma squareWeight_nonneg (xi m : ℕ) : 0 ≤ squareWeight xi m := by
  exact sq_nonneg _

/-- The integer-scaled form of `1 - (1/209) * ∑ τ(Lᵢ(n))`.
Scaling by the positive number `209` avoids divisions in all finite
extraction lemmas. -/
def divisorScore {ι : Type*} [Fintype ι]
    (L : ι → ℕ → ℕ) (n : ℕ) : ℝ :=
  209 - ∑ i, (σ 0 (L i n) : ℝ)

/-- A positive scored nonnegative weight can occur only where the sum of
the eight divisor counts is at most `208`. -/
lemma divisor_sum_le_twoHundredEight_of_score_mul_pos
    (L : Fin 8 → ℕ → ℕ) {w : ℕ → ℝ} {n : ℕ}
    (hw : 0 ≤ w n) (hpos : 0 < divisorScore L n * w n) :
    (∑ i, σ 0 (L i n)) ≤ 208 := by
  have hscore : 0 < divisorScore L n := by
    rcases (mul_pos_iff.mp hpos) with h | h
    · exact h.1
    · exact (not_lt_of_ge hw h.2).elim
  unfold divisorScore at hscore
  have hcast : ((∑ i, σ 0 (L i n) : ℕ) : ℝ) =
      ∑ i, (σ 0 (L i n) : ℝ) := by norm_cast
  rw [← hcast] at hscore
  have hltR : ((∑ i, σ 0 (L i n) : ℕ) : ℝ) < (209 : ℝ) := by
    linarith
  have hlt : (∑ i, σ 0 (L i n)) < 209 := by exact_mod_cast hltR
  omega

/-- Positivity of the complete finite Pinner sum selects a point with
divisor sum at most `208` and with strictly positive square weight. -/
theorem exists_divisor_sum_le_twoHundredEight_of_sum_pos
    {α : Type*} [DecidableEq α] (s : Finset α)
    (L : Fin 8 → α → ℕ) (w : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x)
    (hpos : 0 < ∑ x ∈ s,
      (209 - ∑ i, (σ 0 (L i x) : ℝ)) * w x) :
    ∃ x ∈ s, (∑ i, σ 0 (L i x)) ≤ 208 ∧ 0 < w x := by
  have hex : ∃ x ∈ s,
      0 < (209 - ∑ i, (σ 0 (L i x) : ℝ)) * w x := by
    by_contra hnone
    push Not at hnone
    have hnonpos : (∑ x ∈ s,
        (209 - ∑ i, (σ 0 (L i x) : ℝ)) * w x) ≤ 0 :=
      Finset.sum_nonpos fun x hx ↦ hnone x hx
    exact (not_lt_of_ge hnonpos) hpos
  obtain ⟨x, hxs, hxpos⟩ := hex
  have hxw : 0 < w x := by
    rcases (mul_pos_iff.mp hxpos) with h | h
    · exact h.2
    · exact (not_lt_of_ge (hw x hxs) h.2).elim
  have hscore : 0 < 209 - ∑ i, (σ 0 (L i x) : ℝ) :=
    (mul_pos_iff_of_pos_right hxw).mp hxpos
  have hcast : ((∑ i, σ 0 (L i x) : ℕ) : ℝ) =
      ∑ i, (σ 0 (L i x) : ℝ) := by norm_cast
  rw [← hcast] at hscore
  have hltR : ((∑ i, σ 0 (L i x) : ℕ) : ℝ) < (209 : ℝ) := by
    linarith
  have hlt : (∑ i, σ 0 (L i x)) < 209 := by exact_mod_cast hltR
  exact ⟨x, hxs, by omega, hxw⟩

/-- Specialization to Pinner's actual square weight. -/
theorem exists_divisor_sum_le_twoHundredEight_of_pinner_sum_pos
    (s : Finset ℕ) (L : Fin 8 → ℕ → ℕ) (xi : ℕ)
    (hpos : 0 < ∑ n ∈ s,
      divisorScore L n * squareWeight xi (∏ i, L i n)) :
    ∃ n ∈ s, (∑ i, σ 0 (L i n)) ≤ 208 ∧
      0 < squareWeight xi (∏ i, L i n) := by
  apply exists_divisor_sum_le_twoHundredEight_of_sum_pos s
    (fun i n ↦ L i n) (fun n ↦ squareWeight xi (∏ i, L i n))
  · intro n _hn
    exact squareWeight_nonneg xi _
  · simpa [divisorScore] using hpos

/-- The exact analytic statement left after all finite extraction has been
removed: beyond every threshold, one finite interval and one Selberg cutoff
have positive Pinner score after restricting to squarefree products. -/
def HasPositiveSquarefreePinnerSums (L : Fin 8 → ℕ → ℕ) : Prop :=
  ∀ T : ℕ, ∃ X xi : ℕ, T < X ∧
    0 < ∑ n ∈ (Finset.Ioc T X).filter
        (fun n ↦ Squarefree (∏ i, L i n)),
      divisorScore L n * squareWeight xi (∏ i, L i n)

/-- Positive squarefree Pinner sums imply exactly the unbounded supply datum
used by the final arithmetic construction. -/
theorem supply_data_of_positive_squarefree_sums
    (L : Fin 8 → ℕ → ℕ)
    (hlarge : ∀ i t, t < L i t)
    (hpositive : HasPositiveSquarefreePinnerSums L) :
    ∀ T : ℕ, ∃ t : ℕ, T < t ∧
      (∀ i, 1 < L i t) ∧
      Squarefree (∏ i, L i t) ∧
      (∑ i, σ 0 (L i t)) ≤ 208 := by
  intro T
  obtain ⟨X, xi, hTX, hsum⟩ := hpositive T
  let s := (Finset.Ioc T X).filter
    (fun n ↦ Squarefree (∏ i, L i n))
  obtain ⟨t, hts, htau, _hweight⟩ :=
    exists_divisor_sum_le_twoHundredEight_of_pinner_sum_pos
      s L xi (by simpa [s] using hsum)
  have htmem := Finset.mem_filter.mp hts
  have htIoc := Finset.mem_Ioc.mp htmem.1
  refine ⟨t, htIoc.1, ?_, htmem.2, htau⟩
  intro i
  exact (Nat.one_le_iff_ne_zero.mpr (by omega : t ≠ 0)).trans_lt
    (hlarge i t)

end

end Erdos946.PinnerWeights
