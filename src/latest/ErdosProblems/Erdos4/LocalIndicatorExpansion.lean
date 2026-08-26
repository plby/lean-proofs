import ErdosProblems.Erdos4.LocalFourier

/-!
# Expanding the normalized local basis into residue indicators

The empty output label represents the constant function. An occupied
output label represents one divisibility condition. The empty input row
is exactly the constant row, while every occupied input row has a
uniformly bounded sum of absolute coefficients.
-/

open scoped BigOperators

namespace Erdos4.LocalIndicatorExpansion

open LocalOrthogonality DivisorCoefficients

variable {k : ℕ}

noncomputable def indicator (s : Option (Fin k)) : Option (Fin k) → ℝ
  | none => 1
  | some i => if s = some i then 1 else 0

noncomputable def transition (ell : ℕ) (a : Option (Fin k)) : Option (Fin k) → ℝ
  | none => localWeight ell a * extendedBasis (ell : ℝ) a none
  | some i => localWeight ell a *
      (extendedBasis (ell : ℝ) a (some i) - extendedBasis (ell : ℝ) a none)

theorem indicator_nonneg (s b : Option (Fin k)) : 0 ≤ indicator s b := by
  cases b with
  | none => exact zero_le_one
  | some i => dsimp [indicator]; split_ifs <;> norm_num

theorem indicator_le_one (s b : Option (Fin k)) : indicator s b ≤ 1 := by
  cases b with
  | none => exact le_rfl
  | some i => dsimp [indicator]; split_ifs <;> norm_num

theorem transition_empty (ell : ℕ) (b : Option (Fin k)) :
    transition ell none b = if b = none then 1 else 0 := by
  cases b <;> simp [transition, localWeight, extendedBasis]

theorem local_expansion (ell : ℕ) (a s : Option (Fin k)) :
    (∑ b, transition ell a b * indicator s b) =
      localWeight ell a * extendedBasis (ell : ℝ) a s := by
  classical
  rw [Fintype.sum_option]
  cases s with
  | none => simp [transition, indicator]
  | some i =>
    simp only [transition, indicator, mul_one, Option.some.injEq, mul_ite, mul_zero]
    simp
    ring

theorem abs_transition_none_le {ell : ℕ} (hell : k + 2 ≤ ell) (a : Option (Fin k)) :
    |transition ell a none| ≤ if a = none then 1 else 2 := by
  have hh := LocalFourier.weighted_evaluation_le hell a none
  simpa only [transition, abs_mul, abs_of_nonneg (localWeight_nonneg ell a), mul_comm] using hh

theorem abs_transition_some_le {ell : ℕ} (hell : k + 2 ≤ ell)
    (i j : Fin k) : |transition ell (some i) (some j)| ≤ 4 := by
  have hoccupied := LocalFourier.weighted_evaluation_le hell (some i) (some j)
  have hempty := LocalFourier.weighted_evaluation_le hell (some i) none
  simp only [reduceCtorEq, if_false] at hoccupied hempty
  unfold transition
  rw [abs_mul, abs_of_nonneg (localWeight_nonneg ell (some i))]
  calc
    _ ≤ localWeight ell (some i) *
        (|extendedBasis (ell : ℝ) (some i) (some j)| +
          |extendedBasis (ell : ℝ) (some i) none|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (localWeight_nonneg ell (some i))
    _ ≤ 4 := by nlinarith

noncomputable def rowCost (k : ℕ) : ℝ := 4 * k + 2

theorem rowCost_nonneg (k : ℕ) : 0 ≤ rowCost k := by unfold rowCost; positivity

theorem row_bound {ell : ℕ} (hell : k + 2 ≤ ell) (a : Option (Fin k)) :
    (∑ b, |transition ell a b|) ≤ if a = none then 1 else rowCost k := by
  classical
  cases a with
  | none => simp [transition_empty]
  | some i =>
    simp only [reduceCtorEq, if_false]
    rw [Fintype.sum_option]
    calc
      _ ≤ 2 + ∑ j : Fin k, (4 : ℝ) := add_le_add
        (by simpa only [reduceCtorEq, if_false] using abs_transition_none_le hell (some i))
        (Finset.sum_le_sum (fun j _hj => abs_transition_some_le hell i j))
      _ = rowCost k := by simp [rowCost]; ring

end Erdos4.LocalIndicatorExpansion
