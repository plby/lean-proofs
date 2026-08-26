/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The archimedean upper bound for an evaluation determinant.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

lemma abs_det_le_factorial_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (b : ι → ℝ)
    (hM : ∀ i j, |M i j| ≤ b i) :
    |M.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, b i := by
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  change abv M.det ≤ _
  calc
    _ = abv (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M (σ i) i) :=
      congrArg abv (Matrix.det_apply M)
    _ ≤ ∑ σ : Equiv.Perm ι, abv (Equiv.Perm.sign σ • ∏ i, M (σ i) i) :=
      abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, abv (M (σ i) i) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, b (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.prod_le_prod
      · intro i _
        exact abv.nonneg _
      · intro i _
        exact hM (σ i) i
    _ = _ := by
      simp only [Equiv.prod_comp, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, nsmul_eq_mul]

/-- Monomial rows of degrees `w i` on a box of side `B` give the standard
factorial-times-product determinant estimate. -/
theorem log_abs_det_le {s : ℕ} (hs : 0 < s) (M : Matrix (Fin s) (Fin s) ℝ)
    (hM0 : M.det ≠ 0) (B : ℝ) (hB : 0 < B) (w : Fin s → ℕ)
    (hM : ∀ i j, |M i j| ≤ B ^ w i) :
    Real.log |M.det| ≤ (s : ℝ) * Real.log s + (∑ i, w i : ℕ) * Real.log B := by
  have hbound := abs_det_le_factorial_prod M (fun i => B ^ w i) hM
  rw [Finset.prod_pow_eq_pow_sum, Fintype.card_fin] at hbound
  have hfac : (Nat.factorial s : ℝ) ≤ (s : ℝ) ^ s := by
    exact_mod_cast Nat.factorial_le_pow s
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_right hfac
    (pow_nonneg hB.le (∑ i, w i)))
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hlog := Real.log_le_log (abs_pos.mpr hM0) hbound'
  rw [Real.log_mul (pow_ne_zero _ hsR.ne') (pow_ne_zero _ hB.ne'),
    Real.log_pow, Real.log_pow] at hlog
  exact hlog

#print axioms log_abs_det_le
-- 'Erdos477.Counting.log_abs_det_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
