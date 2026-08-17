import ErdosProblems.Erdos543.MissedEvents

/-!
# From relative Poisson estimates to a second-moment bound

This file turns relative first- and second-order estimates for a finite family
of miss events into a simple quantitative upper bound for the probability that
no target is missed.  The generic theorem uses an arbitrary positive benchmark
`q`; the final theorem specializes it to the Poisson benchmark `exp (-λ)`.
-/

open scoped BigOperators

namespace Erdos543.PoissonSecondMoment

open FiniteProbability MissedEvents

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

/-- Relative singleton and pair errors of size at most `δ` imply a clean
second-moment estimate.  The constants are deliberately coarse and uniform:
for `0 ≤ δ ≤ 1/2`,

`P(no miss event occurs) ≤ 6 / (#ι * q) + 12 δ`.

No symmetry between the individual events is assumed. -/
theorem prob_no_missed_le_of_relative_errors [Nonempty Ω] [Nonempty ι]
    (E : ι → Set Ω) (q δ : ℝ)
    (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ (1 / 2 : ℝ))
    (hsingle : ∀ i, |prob (E i) - q| ≤ δ * q)
    (hpair : ∀ i j, i ≠ j →
      |prob (E i ∩ E j) - q ^ 2| ≤ δ * q ^ 2) :
    prob {ω | missedCount E ω = 0} ≤
      6 / ((Fintype.card ι : ℝ) * q) + 12 * δ := by
  let n : ℝ := Fintype.card ι
  let B : ℝ :=
    n * (q + δ * q) + orderedPairCount ι * (q ^ 2 + δ * q ^ 2) -
      (n * (q - δ * q)) ^ 2
  let D : ℝ := (n * (q - δ * q)) ^ 2
  let U : ℝ := n * q * (1 + δ) + 3 * (n * q) ^ 2 * δ
  let L : ℝ := (n * q) ^ 2 / 4
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hnq : 0 < n * q := mul_pos hn hq
  have hδlt : δ < 1 := lt_of_le_of_lt hδhalf (by norm_num)
  have hrel : δ * q < q := by nlinarith
  have hraw : prob {ω | missedCount E ω = 0} ≤ B / D := by
    simpa [B, D, n] using
      prob_no_missed_le_of_errors E q (δ * q) (δ * q ^ 2)
        hrel hsingle hpair
  have hDpos : 0 < D := by
    dsimp [D]
    have : 0 < n * (q - δ * q) := mul_pos hn (sub_pos.mpr hrel)
    positivity
  have hB_le_U : B ≤ U := by
    have hprefactor :
        0 ≤ n * q ^ 2 * (n * δ ^ 2 + 1 + δ) := by positivity
    dsimp [B, U, orderedPairCount]
    ring_nf at hprefactor ⊢
    nlinarith
  have hU0 : 0 ≤ U := by
    dsimp [U]
    positivity
  have hquarter : (1 / 4 : ℝ) ≤ (1 - δ) ^ 2 := by
    nlinarith [sq_nonneg (δ - 1)]
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  have hL_le_D : L ≤ D := by
    have hmul :
        0 ≤ (n * q) ^ 2 * ((1 - δ) ^ 2 - (1 / 4 : ℝ)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hquarter)
    dsimp [L, D]
    ring_nf at hmul ⊢
    nlinarith
  calc
    prob {ω | missedCount E ω = 0} ≤ B / D := hraw
    _ ≤ U / D := div_le_div_of_nonneg_right hB_le_U hDpos.le
    _ ≤ U / L := div_le_div_of_nonneg_left hU0 hLpos hL_le_D
    _ = 4 * (1 + δ) / (n * q) + 12 * δ := by
      dsimp [U, L]
      field_simp
      ring
    _ ≤ 6 / (n * q) + 12 * δ := by
      have hden : 0 < n * q := hnq
      have hfrac : 4 * (1 + δ) / (n * q) ≤ 6 / (n * q) := by
        rw [div_le_div_iff_of_pos_right hden]
        nlinarith
      linarith
    _ = 6 / ((Fintype.card ι : ℝ) * q) + 12 * δ := by rfl

/-- Poisson-specialized form of
`prob_no_missed_le_of_relative_errors`.  Relative error `δ` around
`exp (-λ)` for singletons and `exp (-2λ)` for distinct pairs gives

`P(no target is missed) ≤ 6 / (#ι * exp (-λ)) + 12 δ`.
-/
theorem prob_no_missed_le_of_relative_exp_errors [Nonempty Ω] [Nonempty ι]
    (E : ι → Set Ω) (lam δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ (1 / 2 : ℝ))
    (hsingle : ∀ i,
      |prob (E i) - Real.exp (-lam)| ≤ δ * Real.exp (-lam))
    (hpair : ∀ i j, i ≠ j →
      |prob (E i ∩ E j) - Real.exp (-2 * lam)| ≤
        δ * Real.exp (-2 * lam)) :
    prob {ω | missedCount E ω = 0} ≤
      6 / ((Fintype.card ι : ℝ) * Real.exp (-lam)) + 12 * δ := by
  let q : ℝ := Real.exp (-lam)
  have hq : 0 < q := by
    dsimp [q]
    exact Real.exp_pos _
  have hq_sq : Real.exp (-2 * lam) = q ^ 2 := by
    dsimp [q]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply prob_no_missed_le_of_relative_errors E q δ hq hδ0 hδhalf
  · intro i
    simpa [q] using hsingle i
  · intro i j hij
    rw [← hq_sq]
    exact hpair i j hij

end

end Erdos543.PoissonSecondMoment
