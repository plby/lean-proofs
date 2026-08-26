import ErdosProblems.Erdos4.ProductOrthogonality
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Contractive restrictions of the product sieve measure

Removing selected residue states is a contraction in the exact coefficient
norm. The bilinear version is used for coefficient slices in the Fourier
argument; no rectangular support or positive coefficient assumption is needed.
-/

open scoped BigOperators

namespace Erdos4.RestrictedProductNorm

open ProductOrthogonality

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def energy (v : (P → Option (Fin k)) → ℝ) : ℝ := ∑ a, v a ^ 2

theorem energy_nonneg (v : (P → Option (Fin k)) → ℝ) : 0 ≤ energy v :=
  Finset.sum_nonneg (fun _a _ha => sq_nonneg _)

noncomputable def restrictedForm (ell : P → ℝ) (mask : (P → Option (Fin k)) → ℝ)
    (v w : (P → Option (Fin k)) → ℝ) : ℝ :=
  mean ell (fun s => mask s * (expansion ell v s * expansion ell w s))

theorem restrictedForm_self_nonneg (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (mask : (P → Option (Fin k)) → ℝ) (hmask : ∀ s, 0 ≤ mask s)
    (v : (P → Option (Fin k)) → ℝ) : 0 ≤ restrictedForm ell mask v v := by
  unfold restrictedForm mean
  apply Finset.sum_nonneg
  intro s _hs
  exact mul_nonneg (stateWeight_nonneg ell hell s)
    (mul_nonneg (hmask s) (mul_self_nonneg _))

theorem restrictedForm_self_le_energy (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (mask : (P → Option (Fin k)) → ℝ) (hmask : ∀ s, mask s ≤ 1)
    (v : (P → Option (Fin k)) → ℝ) : restrictedForm ell mask v v ≤ energy v := by
  have hparseval := mean_expansion_sq ell hell v
  calc
    restrictedForm ell mask v v ≤ mean ell (fun s => expansion ell v s ^ 2) := by
      unfold restrictedForm mean
      apply Finset.sum_le_sum
      intro s _hs
      apply mul_le_mul_of_nonneg_left _ (stateWeight_nonneg ell hell s)
      simpa only [pow_two, one_mul] using
        mul_le_mul_of_nonneg_right (hmask s) (mul_self_nonneg (expansion ell v s))
    _ = energy v := hparseval

/-- Cauchy--Schwarz for the restricted product measure, including vanishing
weights and empty prime-index sets. -/
theorem restrictedForm_sq_le (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (mask : (P → Option (Fin k)) → ℝ) (hmask : ∀ s, 0 ≤ mask s)
    (v w : (P → Option (Fin k)) → ℝ) :
    restrictedForm ell mask v w ^ 2 ≤
      restrictedForm ell mask v v * restrictedForm ell mask w w := by
  unfold restrictedForm mean
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro s _hs
    exact mul_nonneg (stateWeight_nonneg ell hell s)
      (mul_nonneg (hmask s) (mul_self_nonneg _))
  · intro s _hs
    exact mul_nonneg (stateWeight_nonneg ell hell s)
      (mul_nonneg (hmask s) (mul_self_nonneg _))
  · intro s _hs
    apply le_of_eq
    ring

theorem restrictedForm_sq_le_energy (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (mask : (P → Option (Fin k)) → ℝ) (hmask0 : ∀ s, 0 ≤ mask s)
    (hmask1 : ∀ s, mask s ≤ 1) (v w : (P → Option (Fin k)) → ℝ) :
    restrictedForm ell mask v w ^ 2 ≤ energy v * energy w := by
  exact (restrictedForm_sq_le ell hell mask hmask0 v w).trans
    (mul_le_mul (restrictedForm_self_le_energy ell hell mask hmask1 v)
      (restrictedForm_self_le_energy ell hell mask hmask1 w)
      (restrictedForm_self_nonneg ell hell mask hmask0 w) (energy_nonneg v))

theorem abs_restrictedForm_le (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (mask : (P → Option (Fin k)) → ℝ) (hmask0 : ∀ s, 0 ≤ mask s)
    (hmask1 : ∀ s, mask s ≤ 1) (v w : (P → Option (Fin k)) → ℝ) :
    |restrictedForm ell mask v w| ≤ Real.sqrt (energy v) * Real.sqrt (energy w) := by
  have hsq := restrictedForm_sq_le_energy ell hell mask hmask0 hmask1 v w
  have hv := Real.sq_sqrt (energy_nonneg v)
  have hw := Real.sq_sqrt (energy_nonneg w)
  have hprod : 0 ≤ Real.sqrt (energy v) * Real.sqrt (energy w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hprod_sq : (Real.sqrt (energy v) * Real.sqrt (energy w)) ^ 2 = energy v * energy w := by
    rw [mul_pow, hv, hw]
  rw [← hprod_sq] at hsq
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end Erdos4.RestrictedProductNorm
