/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.ShiftedGaussian
import ErdosProblems.Erdos622.TwoLargeForest

/-!
# Finite powerset counts for the shifted two-large window

This small interface exposes the compact shifted-Gaussian calculation in the
exact quantifier order consumed by the two-large-cover argument: the additive
shrink and margin are fixed first, uniformly over the balanced cut and both
compact parameters.
-/

open Filter Set

namespace Erdos622.ShiftedWindowCount

attribute [local instance] Classical.propDecidable

/-- For every compact positive range of `alpha`, one fixed additive loss
`rho` may be removed from both shifted capacities while retaining, uniformly
over `kappa in [0,1]`, more than half of all subsets of every balanced cut. -/
theorem eventually_uniform_balancedCut_shrunken_capacity_count
    {η M : ℝ} (hη : 0 < η) (hηM : η ≤ M) :
    ∃ ρ margin : ℝ, 0 < ρ ∧ 0 < margin ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ A B : Finset (Fin (2 * n)), IsCut A B →
          A.card = n → B.card = n →
          ∀ α ∈ Icc η M, ∀ κ ∈ Icc (0 : ℝ) 1,
            (1 / 2 : ℝ) + margin / 2 <
              (almostBipartiteCount
                (Finset.univ : Finset (Fin (2 * n)))
                (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
                  ((S ∩ A).card + (n - (S ∩ B).card)) ∈
                    Icc
                      (-((max (α / 4 - κ) (15 * κ) - ρ) * Real.sqrt 2))
                      ((max (1 / α) κ - ρ) * Real.sqrt 2)) : ℝ) /
                (2 : ℝ) ^ (2 * n) := by
  obtain ⟨ρ, margin, hρ, _hρone, hmargin, huniform⟩ :=
    ShiftedGaussian.eventually_uniform_balancedCut_shrunken_capacity_difference_count
      hη hηM
  exact ⟨ρ, margin, hρ, hmargin, huniform⟩

/-! ## Concentration of the balancing set -/

/-- The integer square root tends to infinity. -/
lemma tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

/-- Exponential decay on the integer-square-root scale. -/
lemma tendsto_exp_neg_nat_sqrt (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-c * (Nat.sqrt n : ℝ)))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_sqrt_atTop
  have hscale : Tendsto (fun n : ℕ ↦ c * (Nat.sqrt n : ℝ))
      atTop atTop := hsqrt.const_mul_atTop hc
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale using 1
  ext n
  simp

/-- Uniformly over every balancing set of size at most `floor (sqrt n)`,
the proportion of subsets whose intersection with the balancing set differs
from its mean by at least `rho * floor (sqrt n)` tends to zero. -/
theorem eventually_balancingSet_bad_count_le
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ T : Finset (Fin (2 * n)), T.card ≤ Nat.sqrt n →
        ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
            ρ * (Nat.sqrt n : ℝ) ≤
              |SamplingSuitable.intersectionCount T S -
                (T.card : ℝ) / 2|).card : ℝ)) ≤
          δ * (2 : ℝ) ^ (2 * n) := by
  have hc : 0 < 2 * ρ ^ 2 := by positivity
  have htailTendsto : Tendsto
      (fun n : ℕ ↦ 2 * Real.exp (-(2 * ρ ^ 2) * (Nat.sqrt n : ℝ)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_exp_neg_nat_sqrt (2 * ρ ^ 2) hc).const_mul 2
  have htail : ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (-(2 * ρ ^ 2) * (Nat.sqrt n : ℝ)) < δ :=
    htailTendsto.eventually_lt_const hδ
  filter_upwards [eventually_ge_atTop 1, htail] with n hn htailn
  intro T hT
  have hsqrtNat : 0 < Nat.sqrt n := by
    rw [Nat.sqrt_pos]
    omega
  have ht : 0 < ρ * (Nat.sqrt n : ℝ) := by positivity
  have hraw := TwoLargeForest.intersectionCount_twoSided_of_card_le
    T hT hsqrtNat ht
  have hexponent :
      -2 * (ρ * (Nat.sqrt n : ℝ)) ^ 2 / (Nat.sqrt n : ℝ) =
        -(2 * ρ ^ 2) * (Nat.sqrt n : ℝ) := by
    have hsqrtReal : (0 : ℝ) < Nat.sqrt n := by exact_mod_cast hsqrtNat
    field_simp [ne_of_gt hsqrtReal]
  rw [Fintype.card_fin, hexponent] at hraw
  calc
    _ ≤ 2 * (2 : ℝ) ^ (2 * n) *
        Real.exp (-(2 * ρ ^ 2) * (Nat.sqrt n : ℝ)) := hraw
    _ = (2 * Real.exp (-(2 * ρ ^ 2) * (Nat.sqrt n : ℝ))) *
        (2 : ℝ) ^ (2 * n) := by ring
    _ ≤ δ * (2 : ℝ) ^ (2 * n) := by
      exact mul_le_mul_of_nonneg_right htailn.le (by positivity)

end Erdos622.ShiftedWindowCount
