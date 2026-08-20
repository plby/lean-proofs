/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.External.Erdos439.Main
import ErdosProblems.Erdos446.UpperPowerfulReduction

/-!
# Erdős Problem 446: divisor-weighted powerful mass

Ford's squarefull removal requires the convergent sum
`sum_{q powerful} tau(q)/q`.  We derive it from the repository's uniform
subpower divisor bound and the already established `9/16` powerful
Dirichlet mass.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

local instance powerfulWeightedMassDecidable :
    DecidablePred Erdos469.Powerful := Classical.decPred _

theorem exists_divisorCard_div_le_powerfulWeight :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ q : ℕ, 1 ≤ q → Erdos469.Powerful q →
      ((q.divisors.card : ℕ) : ℝ) / (q : ℝ) ≤
        (M : ℝ) * Erdos469.powerfulDirichletWeight (9 / 16 : ℝ) q := by
  obtain ⟨M₁, hM₁⟩ := Erdos443.divisor_bound 1 (by norm_num)
  obtain ⟨M₂, hM₂⟩ :=
    Erdos439.PowerDecay.eventual_divisor_exponent_le 1 (by omega)
  let M := max 1 (max M₁ M₂)
  have hM : 1 ≤ M := by simp [M]
  refine ⟨M, hM, fun q hq hqPow ↦ ?_⟩
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans_le hqR
  rw [Erdos469.powerfulDirichletWeight, if_pos hqPow]
  by_cases hlarge : M ≤ q
  · have hM₁q : M₁ ≤ q := (le_max_left M₁ M₂).trans
        (le_max_right 1 (max M₁ M₂) |>.trans hlarge)
    have hM₂q : M₂ ≤ q := (le_max_right M₁ M₂).trans
        (le_max_right 1 (max M₁ M₂) |>.trans hlarge)
    have hdiv := (hM₁ q hM₁q).le
    have hexp := hM₂ q hM₂q
    norm_num at hexp
    have hexp' :
        (1 + (1 : ℝ)) * Real.log 2 / Real.log (Real.log (q : ℝ)) ≤
          1 / 8 := by
      convert hexp using 1 <;> norm_num
    have hpow : (q.divisors.card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) :=
      hdiv.trans (Real.rpow_le_rpow_of_exponent_le hqR hexp')
    have hquot : (q.divisors.card : ℝ) / (q : ℝ) ≤
        (q : ℝ) ^ (-(7 / 8 : ℝ)) := by
      calc
        (q.divisors.card : ℝ) / (q : ℝ) ≤
            (q : ℝ) ^ (1 / 8 : ℝ) / (q : ℝ) := by
          exact div_le_div_of_nonneg_right hpow hqPos.le
        _ = (q : ℝ) ^ (-(7 / 8 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hqPos]
          norm_num
    have hweight : (q : ℝ) ^ (-(7 / 8 : ℝ)) ≤
        (q : ℝ) ^ (-(9 / 16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hqR (by norm_num)
    calc
      (q.divisors.card : ℝ) / (q : ℝ) ≤
          (q : ℝ) ^ (-(9 / 16 : ℝ)) := hquot.trans hweight
      _ ≤ (M : ℝ) * (q : ℝ) ^ (-(9 / 16 : ℝ)) := by
        exact le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (by exact_mod_cast hM)
  · have hqM : q ≤ M := by omega
    have hcard : (q.divisors.card : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self q
    have hterm : (q.divisors.card : ℝ) / (q : ℝ) ≤ 1 := by
      exact (div_le_one hqPos).2 hcard
    have hpowLe : (q : ℝ) ^ (9 / 16 : ℝ) ≤ (M : ℝ) := by
      calc
        (q : ℝ) ^ (9 / 16 : ℝ) ≤ (q : ℝ) :=
          Real.rpow_le_self_of_one_le hqR (by norm_num)
        _ ≤ (M : ℝ) := by exact_mod_cast hqM
    have hone : (1 : ℝ) ≤
        (M : ℝ) * (q : ℝ) ^ (-(9 / 16 : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg q) (9 / 16 : ℝ)]
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hqPos _)).2
        (by simpa using hpowLe)
    exact hterm.trans hone

/-- Uniform convergence of the divisor-weighted powerful partial sums. -/
theorem exists_pos_sum_divisorCard_div_powerful_le :
    ∃ D : ℝ, 0 < D ∧ ∀ Q : ℕ,
      (∑ q ∈ (Finset.Icc 1 Q).filter Erdos469.Powerful,
        ((q.divisors.card : ℕ) : ℝ) / (q : ℝ)) ≤ D := by
  obtain ⟨M, hM, hpoint⟩ := exists_divisorCard_div_le_powerfulWeight
  let D : ℝ :=
    (M : ℝ) * Erdos469.powerfulNineSixteenthsMass + 1
  have hD : 0 < D := by
    dsimp [D]
    have hmass := Erdos469.powerfulNineSixteenthsMass_nonneg
    positivity
  refine ⟨D, hD, fun Q ↦ ?_⟩
  let s := (Finset.Icc 1 Q).filter Erdos469.Powerful
  have hfinite :
      (∑ q ∈ s, Erdos469.powerfulDirichletWeight (9 / 16 : ℝ) q) ≤
        Erdos469.powerfulNineSixteenthsMass := by
    exact Erdos469.powerfulNineSixteenthsMass_summable.sum_le_tsum s
      (fun q hq ↦ Erdos469.powerfulDirichletWeight_nonneg _ q)
  calc
    (∑ q ∈ (Finset.Icc 1 Q).filter Erdos469.Powerful,
        ((q.divisors.card : ℕ) : ℝ) / (q : ℝ)) ≤
      ∑ q ∈ s,
        (M : ℝ) * Erdos469.powerfulDirichletWeight (9 / 16 : ℝ) q := by
      apply Finset.sum_le_sum
      intro q hq
      exact hpoint q (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
        (Finset.mem_filter.mp hq).2
    _ = (M : ℝ) *
        (∑ q ∈ s, Erdos469.powerfulDirichletWeight (9 / 16 : ℝ) q) := by
      rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * Erdos469.powerfulNineSixteenthsMass := by
      gcongr
    _ ≤ D := by dsimp [D]; linarith

end

end Erdos446
