/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionBox
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionNumerics

/-!
# Adjugate bounds from a containing integer box

Replacing one row of the square step matrix by a standard basis row turns
its determinant into an adjugate entry.  The anisotropic determinant bound
then controls that entry after multiplying by all the other progression
widths.  This is the quantitative inverse estimate used in the residual
absorption argument.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Product of all active displayed widths except coordinate `i`. -/
def widthProductExcept {d : ℕ} (P : GAP d d) (i : Fin d) : ℕ :=
  ∏ k ∈ Finset.univ.erase i, (P.widths k - 1)

/-- One adjugate entry, multiplied by all other displayed widths, is bounded
by the factorial times the cardinality of a containing integer box. -/
theorem adjugate_entry_mul_widthProductExcept_le_factorial_mul_boxCard
    {d : ℕ} (P : GAP d d) (B : CFP.IntegerBox d)
    (t : LatticePoint d)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (i j : Fin d) :
    ((stepMatrix P).adjugate j i).natAbs * widthProductExcept P i ≤
      d.factorial * B.carrier.card := by
  let M := stepMatrix P
  let A : Matrix (Fin d) (Fin d) ℤ := M.updateRow i (Pi.single j 1)
  let s : Fin d → ℝ := fun k ↦
    if k = i then 1 else (P.widths k - 1 : ℕ)
  let u : Fin d → ℝ := fun l ↦
    ((B.upper l - B.lower l : ℤ) : ℝ) + 1
  have hB := integerBox_lower_le_upper_of_gap_containment P B t hcontain
  have hs : ∀ k, 0 ≤ s k := by
    intro k
    simp only [s]
    split <;> positivity
  have hentry : ∀ k l, s k * |(A k l : ℝ)| ≤ u l := by
    intro k l
    by_cases hki : k = i
    · subst k
      simp only [s, if_pos, one_mul, A, Matrix.updateRow_self]
      have hside : (0 : ℝ) ≤
          ((B.upper l - B.lower l : ℤ) : ℝ) := by
        exact_mod_cast sub_nonneg.mpr (hB l)
      by_cases hjl : j = l
      · subst l
        simp only [Pi.single_eq_same, Int.cast_one, abs_one, u]
        linarith
      · have hlj : l ≠ j := fun h ↦ hjl h.symm
        simp only [Pi.single_apply, hlj, ↓reduceIte, Int.cast_zero, abs_zero,
          u]
        linarith
    · simp only [s, if_neg hki, A, Matrix.updateRow_ne hki]
      calc
        ((P.widths k - 1 : ℕ) : ℝ) * |(M k l : ℝ)| ≤
            ((B.upper l - B.lower l : ℤ) : ℝ) := by
          simpa only [M, stepMatrix] using
            scaled_step_abs_cast_le_box_side P B t hcontain k l
        _ ≤ u l := by simp [u]
  have hdet := natAbs_det_mul_prod_le A s u hs hentry
  have hprodS : (∏ k, s k) = (widthProductExcept P i : ℝ) := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (Finset.mem_univ i) s]
    simp only [s, if_pos, one_mul]
    rw [show Finset.univ \ {i} = Finset.univ.erase i by ext k; simp]
    unfold widthProductExcept
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp [s, hki]
  have hprodU : (∏ l, u l) = (B.carrier.card : ℝ) := by
    rw [B.card_carrier]
    push_cast
    apply Finset.prod_congr rfl
    intro l _hl
    have hl := hB l
    have hnonneg : 0 ≤ B.upper l + 1 - B.lower l := by omega
    have hcast :
        (((B.upper l + 1 - B.lower l).toNat : ℕ) : ℝ) =
          ((B.upper l + 1 - B.lower l : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast]
    simp only [u]
    push_cast
    ring
  have hdetA : A.det = (stepMatrix P).adjugate j i := by
    simpa only [A, M] using (Matrix.adjugate_apply (stepMatrix P) j i).symm
  rw [hdetA, hprodS, hprodU] at hdet
  exact_mod_cast hdet

/-- Summing over the ambient coordinates costs one factor of the dimension. -/
theorem sum_adjugate_mul_widthProductExcept_le
    {d : ℕ} (P : GAP d d) (B : CFP.IntegerBox d)
    (t : LatticePoint d)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (i : Fin d) :
    (∑ j, ((stepMatrix P).adjugate j i).natAbs) *
        widthProductExcept P i ≤
      d * (d.factorial * B.carrier.card) := by
  calc
    (∑ j, ((stepMatrix P).adjugate j i).natAbs) *
        widthProductExcept P i =
        ∑ j, ((stepMatrix P).adjugate j i).natAbs *
          widthProductExcept P i := by rw [Finset.sum_mul]
    _ ≤ ∑ _j : Fin d, d.factorial * B.carrier.card := by
      exact Finset.sum_le_sum fun j _ ↦
        adjugate_entry_mul_widthProductExcept_le_factorial_mul_boxCard
          P B t hcontain i j
    _ = d * (d.factorial * B.carrier.card) := by simp

end

end Erdos186.PZ.Intersection
