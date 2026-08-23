/- leanprover/lean4:v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.InterpolationProducts

/-!
# Stable sharp nodal quotient for source Lemma 4

This small module isolates the elementary `3^(-R*S)` quotient from the
source-parameter arithmetic.  A genuinely new target `Rold < l` can be
paired with each old node in the numerator and denominator, giving a factor
`1/3` on the outer circle of radius `3*Rnext`.
-/

open scoped BigOperators

open Complex Finset

noncomputable section

namespace Erdos240.InterpolationProducts

/-- At a genuinely new target, the target-to-node distance is at most one
third of the outer-circle-to-node distance. -/
theorem three_mul_norm_target_sub_node_le_outer_sharp
    {Rold Rnext l r : ℕ} {z : ℂ}
    (hr : r ≤ Rold) (hRold : Rold < l) (hl : l ≤ Rnext)
    (hz : ‖z‖ = 3 * Rnext) :
    3 * ‖(l : ℂ) - (r : ℂ)‖ ≤ ‖z - (r : ℂ)‖ := by
  have hrl : r ≤ l := hr.trans hRold.le
  have hnum : ‖(l : ℂ) - (r : ℂ)‖ = (l : ℝ) - r := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast hrl)
  have hrnext : (r : ℝ) ≤ Rnext := by
    exact_mod_cast hr.trans (hRold.le.trans hl)
  have hden : 3 * (Rnext : ℝ) - r ≤ ‖z - (r : ℂ)‖ := by
    calc
      3 * (Rnext : ℝ) - r = ‖z‖ - ‖(r : ℂ)‖ := by
        simp only [hz, Complex.norm_natCast]
      _ ≤ ‖z - (r : ℂ)‖ := norm_sub_norm_le _ _
  rw [hnum]
  have hnumden : 3 * ((l : ℝ) - r) ≤ 3 * Rnext - r := by
    have hl' : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    linarith
  exact hnumden.trans hden

/-- The exact new-target quotient `3^(-Rold*S)` on the outer circle. -/
theorem norm_integralNodalProduct_newTarget_div_outerCircle_le_sharp
    {Rold Rnext S l : ℕ} {z : ℂ}
    (hRold : Rold < l) (hl : l ≤ Rnext)
    (hz : ‖z‖ = 3 * Rnext) :
    ‖integralNodalProduct Rold S (l : ℂ) /
        integralNodalProduct Rold S z‖ ≤
      (1 / 3 : ℝ) ^ (Rold * S) := by
  rw [integralNodalProduct, integralNodalProduct,
    ← Finset.prod_div_distrib, norm_prod]
  calc
    ∏ i ∈ range Rold,
        ‖((l : ℂ) - (i + 1 : ℕ)) ^ S /
          (z - (i + 1 : ℕ)) ^ S‖ ≤
        ∏ _i ∈ range Rold, (1 / 3 : ℝ) ^ S := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hir : i + 1 ≤ Rold := Nat.succ_le_iff.mpr (mem_range.mp hi)
        have hdist := three_mul_norm_target_sub_node_le_outer_sharp
          hir hRold hl hz
        have hden : 0 < ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
          have hnode : ((i + 1 : ℕ) : ℝ) < 3 * Rnext := by
            have hiRnext : i + 1 ≤ Rnext :=
              hir.trans (hRold.le.trans hl)
            have hRnext : 0 < Rnext := lt_of_lt_of_le (by omega) hl
            exact_mod_cast (show i + 1 < 3 * Rnext by omega)
          rw [norm_pos_iff, sub_ne_zero]
          intro h
          have := congrArg norm h
          simp only [hz, Complex.norm_natCast] at this
          linarith
        have hbase :
            ‖((l : ℂ) - (i + 1 : ℕ)) /
                (z - (i + 1 : ℕ))‖ ≤ (1 / 3 : ℝ) := by
          rw [norm_div, div_le_iff₀ hden]
          nlinarith
        rw [← div_pow, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hbase S
    _ = (1 / 3 : ℝ) ^ (Rold * S) := by
      rw [Finset.prod_const, card_range, mul_comm Rold S, pow_mul]

end Erdos240.InterpolationProducts

#print axioms Erdos240.InterpolationProducts.three_mul_norm_target_sub_node_le_outer_sharp
#print axioms Erdos240.InterpolationProducts.norm_integralNodalProduct_newTarget_div_outerCircle_le_sharp
