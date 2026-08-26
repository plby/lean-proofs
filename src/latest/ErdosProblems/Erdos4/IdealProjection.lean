import ErdosProblems.Erdos4.ProjectionKernel
import ErdosProblems.Erdos4.CoefficientMass

/-!
# The positive ideal one-prime projection

The ideal normal is supported on the empty label and the anchor label.
Its deletion projection has nonnegative entries and preserves every other
coordinate label. These are the properties needed for the harmonic-sum
lower bound on the actual cutoff vector.
-/

open scoped BigOperators

namespace Erdos4.IdealProjection

variable {k : ℕ}

noncomputable def normal (ell : ℝ) (j : Fin k) : Option (Fin k) → ℝ
  | none => 1 / Real.sqrt ell
  | some i => if i = j then -Real.sqrt (ell - 1) / Real.sqrt ell else 0

theorem normal_norm_one {ell : ℝ} (hell : 1 < ell) (j : Fin k) :
    (∑ a, normal ell j a ^ 2) = 1 := by
  have he : 0 < ell := lt_trans zero_lt_one hell
  have hs := Real.sq_sqrt he.le
  have ht := Real.sq_sqrt (sub_pos.mpr hell).le
  rw [Fintype.sum_option]
  simp only [normal]
  simp only [ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [div_pow, div_pow, one_pow, neg_sq, hs, ht]
  field_simp
  ring

noncomputable def kernel (ell : ℝ) (j : Fin k) : Option (Fin k) → Option (Fin k) → ℝ :=
  ProjectionKernel.kernel (normal ell j)

theorem kernel_none_none {ell : ℝ} (hell : 1 < ell) (j : Fin k) :
    kernel ell j none none = (ell - 1) / ell := by
  have he : 0 < ell := lt_trans zero_lt_one hell
  simp only [kernel, ProjectionKernel.kernel, normal, ↓reduceIte]
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt he.le]
  field_simp

theorem kernel_none_anchor {ell : ℝ} (hell : 1 < ell) (j : Fin k) :
    kernel ell j none (some j) = Real.sqrt (ell - 1) / ell := by
  have he : 0 < ell := lt_trans zero_lt_one hell
  simp only [kernel, ProjectionKernel.kernel, normal, reduceCtorEq, ↓reduceIte, zero_sub]
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt he.le]
  ring

theorem kernel_anchor_none {ell : ℝ} (hell : 1 < ell) (j : Fin k) :
    kernel ell j (some j) none = Real.sqrt (ell - 1) / ell := by
  rw [kernel, ProjectionKernel.kernel_symm]
  exact kernel_none_anchor hell j

theorem kernel_anchor_anchor {ell : ℝ} (hell : 1 < ell) (j : Fin k) :
    kernel ell j (some j) (some j) = 1 / ell := by
  have he : 0 < ell := lt_trans zero_lt_one hell
  simp only [kernel, ProjectionKernel.kernel, normal, ↓reduceIte]
  rw [div_mul_div_comm, neg_mul_neg, Real.mul_self_sqrt he.le,
    Real.mul_self_sqrt (sub_pos.mpr hell).le]
  field_simp
  ring

theorem kernel_other_left (ell : ℝ) (j i : Fin k) (hij : i ≠ j) (b : Option (Fin k)) :
    kernel ell j (some i) b = if some i = b then 1 else 0 := by
  simp only [kernel, ProjectionKernel.kernel, normal, if_neg hij, zero_mul, sub_zero]

theorem kernel_other_right (ell : ℝ) (j i : Fin k) (hij : i ≠ j) (a : Option (Fin k)) :
    kernel ell j a (some i) = if a = some i then 1 else 0 := by
  simp only [kernel, ProjectionKernel.kernel, normal, if_neg hij, mul_zero, sub_zero]

/-- Entrywise positivity permits discarding any coefficient-energy subset. -/
theorem kernel_nonneg {ell : ℝ} (hell : 1 < ell) (j : Fin k) (a b : Option (Fin k)) :
    0 ≤ kernel ell j a b := by
  have he : 0 ≤ ell := (lt_trans zero_lt_one hell).le
  cases a with
  | none =>
    cases b with
    | none => rw [kernel_none_none hell j]; exact div_nonneg (sub_pos.mpr hell).le he
    | some i =>
      by_cases hij : i = j
      · subst i
        rw [kernel_none_anchor hell j]
        exact div_nonneg (Real.sqrt_nonneg _) he
      · rw [kernel_other_right ell j i hij]
        simp
  | some i =>
    by_cases hij : i = j
    · subst i
      cases b with
      | none => rw [kernel_anchor_none hell j]; exact div_nonneg (Real.sqrt_nonneg _) he
      | some a =>
        by_cases haj : a = j
        · subst a
          rw [kernel_anchor_anchor hell j]
          exact div_nonneg zero_le_one he
        · rw [kernel_other_right ell j a haj]
          split_ifs <;> norm_num
    · rw [kernel_other_left ell j i hij]
      split_ifs <;> norm_num

def freeze (j : Fin k) (a : Option (Fin k)) : Option (Fin k) :=
  if a = some j then none else a

theorem freeze_eq_none_iff (j : Fin k) (a : Option (Fin k)) :
    freeze j a = none ↔ a = none ∨ a = some j := by
  by_cases ha : a = some j <;> simp [freeze, ha]

theorem kernel_eq_zero_of_freeze_ne (ell : ℝ) (j : Fin k) (a b : Option (Fin k))
    (hab : freeze j a ≠ freeze j b) : kernel ell j a b = 0 := by
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some i =>
      have hij : i ≠ j := by intro hh; subst i; simp [freeze] at hab
      simp [kernel_other_right ell j i hij]
  | some i =>
    by_cases hij : i = j
    · subst i
      cases b with
      | none => simp [freeze] at hab
      | some a =>
        have haj : a ≠ j := by intro hh; subst a; exact (hab rfl).elim
        simp [kernel_other_right ell j a haj, Ne.symm haj]
    · rw [kernel_other_left ell j i hij]
      split_ifs with heq
      · subst b
        exact (hab rfl).elim
      · rfl

theorem freeze_eq_some_iff (j i : Fin k) (hij : i ≠ j) (a : Option (Fin k)) :
    freeze j a = some i ↔ a = some i := by
  by_cases ha : a = some j
  · subst a
    simp [freeze, Ne.symm hij]
  · simp [freeze, ha]

/-- After multiplication by a divisor normalization, the ideal kernel
separates the output label from a reciprocal-totient input factor. -/
theorem weighted_kernel_formula {ell : ℕ} (hell : 2 ≤ ell) (j : Fin k)
    (a b : Option (Fin k)) :
    kernel (ell : ℝ) j a b * DivisorCoefficients.localWeight ell b =
      if freeze j a = freeze j b then
        DivisorCoefficients.localWeight ell a *
          (if freeze j a = none then ((ell : ℝ) - 1) / ell *
            DivisorCoefficients.localWeight ell b ^ 2 else 1)
      else 0 := by
  have he : (1 : ℝ) < ell := by exact_mod_cast hell
  have hs : 0 < Real.sqrt ((ell : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hd : (ell : ℝ) - 1 ≠ 0 := by linarith
  have hs2 := Real.sq_sqrt (show 0 ≤ (ell : ℝ) - 1 by linarith)
  cases a with
  | none =>
    cases b with
    | none => simp [freeze, kernel_none_none he j, DivisorCoefficients.localWeight]
    | some i =>
      by_cases hij : i = j
      · subst i
        rw [kernel_none_anchor he j]
        simp only [freeze, reduceCtorEq, ↓reduceIte, DivisorCoefficients.localWeight,
          one_mul]
        field_simp
        nlinarith
      · simp [freeze, hij, kernel_other_right (ell : ℝ) j i hij]
  | some i =>
    by_cases hij : i = j
    · subst i
      cases b with
      | none =>
        rw [kernel_anchor_none he j]
        simp only [freeze, reduceCtorEq, ↓reduceIte, DivisorCoefficients.localWeight,
          one_pow, mul_one]
        field_simp
        nlinarith
      | some a =>
        by_cases haj : a = j
        · subst a
          rw [kernel_anchor_anchor he j, CoefficientMass.localWeight_some_sq (by omega) j]
          simp only [freeze, ↓reduceIte]
          field_simp
        · simp [freeze, haj, kernel_other_right (ell : ℝ) j a haj, Ne.symm haj]
    · cases b with
      | none => simp [freeze, hij, kernel_other_left (ell : ℝ) j i hij]
      | some a =>
        by_cases haj : a = j
        · subst a
          simp [freeze, hij, kernel_other_left (ell : ℝ) j i hij]
        · simp [freeze, hij, haj, kernel_other_left (ell : ℝ) j i hij,
            DivisorCoefficients.localWeight, ite_mul]

end Erdos4.IdealProjection
