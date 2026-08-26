import ErdosProblems.Erdos4.DivisorCoefficients
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A coarse but sufficient cutoff-mass bound

Inserting the square of the total divisor converts the cutoff sum into a
convergent Euler product. This gives an `O(R^2)` bound with a uniform
constant once the lower prime cutoff is large. No estimate for the
average order of a divisor function is required.
-/

open scoped BigOperators

namespace Erdos4.CutoffMass

open DivisorCoefficients

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def labelCost (B : ℝ) (a : P → Option (Fin k)) : ℝ :=
  ∏ p, if a p = none then 1 else B

noncomputable def scaledCost (ell : P → ℕ) (B : ℝ) (a : P → Option (Fin k)) : ℝ :=
  ∏ p, if a p = none then 1 else B / (ell p : ℝ) ^ 2

noncomputable def mass (R : ℕ) (ell : P → ℕ) (B : ℝ) : ℝ :=
  ∑ a : P → Option (Fin k), if totalDivisor ell a ≤ R then labelCost B a else 0

theorem labelCost_nonneg {B : ℝ} (hB : 0 ≤ B) (a : P → Option (Fin k)) :
    0 ≤ labelCost B a := by
  apply Finset.prod_nonneg
  intro p _hp
  split_ifs <;> first | exact zero_le_one | exact hB

theorem scaledCost_nonneg (ell : P → ℕ) {B : ℝ} (hB : 0 ≤ B) (a : P → Option (Fin k)) :
    0 ≤ scaledCost ell B a := by
  apply Finset.prod_nonneg
  intro p _hp
  split_ifs
  · exact zero_le_one
  · exact div_nonneg hB (sq_nonneg _)

theorem scaledCost_eq (ell : P → ℕ) (B : ℝ) (a : P → Option (Fin k)) :
    scaledCost ell B a = labelCost B a / (totalDivisor ell a : ℝ) ^ 2 := by
  unfold scaledCost labelCost totalDivisor
  rw [Nat.cast_prod, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases ha : a p = none <;> simp [ha]

theorem pointwise_bound (R : ℕ) (ell : P → ℕ) (hell : ∀ p, 0 < ell p)
    {B : ℝ} (hB : 0 ≤ B) (a : P → Option (Fin k)) :
    (if totalDivisor ell a ≤ R then labelCost B a else 0) ≤
      (R : ℝ) ^ 2 * scaledCost ell B a := by
  by_cases ha : totalDivisor ell a ≤ R
  · rw [if_pos ha, scaledCost_eq]
    have hd : (0 : ℝ) < totalDivisor ell a := by exact_mod_cast totalDivisor_pos ell hell a
    have hle : (totalDivisor ell a : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 :=
      pow_le_pow_left₀ hd.le (by exact_mod_cast ha) 2
    calc
      _ = (totalDivisor ell a : ℝ) ^ 2 *
          (labelCost B a / (totalDivisor ell a : ℝ) ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hle
        (div_nonneg (labelCost_nonneg hB a) (sq_nonneg _))
  · rw [if_neg ha]
    exact mul_nonneg (sq_nonneg _) (scaledCost_nonneg ell hB a)

theorem sum_scaledCost (ell : P → ℕ) (B : ℝ) :
    (∑ a : P → Option (Fin k), scaledCost ell B a) =
      ∏ p, (1 + (k : ℝ) * B / (ell p : ℝ) ^ 2) := by
  classical
  unfold scaledCost
  rw [← Fintype.prod_sum (fun p (a : Option (Fin k)) =>
    if a = none then (1 : ℝ) else B / (ell p : ℝ) ^ 2)]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [Fintype.sum_option]
  simp only [reduceCtorEq, if_false, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem mass_le_euler (R : ℕ) (ell : P → ℕ) (hell : ∀ p, 0 < ell p)
    {B : ℝ} (hB : 0 ≤ B) :
    mass (k := k) R ell B ≤ (R : ℝ) ^ 2 *
      ∏ p, (1 + (k : ℝ) * B / (ell p : ℝ) ^ 2) := by
  unfold mass
  calc
    _ ≤ ∑ a : P → Option (Fin k), (R : ℝ) ^ 2 * scaledCost ell B a :=
      Finset.sum_le_sum (fun a _ha => pointwise_bound R ell hell hB a)
    _ = _ := by rw [← Finset.mul_sum, sum_scaledCost]

theorem euler_le_exp (ell : P → ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (∏ p, (1 + (k : ℝ) * B / (ell p : ℝ) ^ 2)) ≤
      Real.exp ((k : ℝ) * B * ∑ p, 1 / (ell p : ℝ) ^ 2) := by
  calc
    _ ≤ ∏ p, Real.exp ((k : ℝ) * B / (ell p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p _hp
        exact add_nonneg zero_le_one (div_nonneg (mul_nonneg (Nat.cast_nonneg k) hB) (sq_nonneg _))
      · intro p _hp
        simpa only [add_comm] using Real.add_one_le_exp ((k : ℝ) * B / (ell p : ℝ) ^ 2)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _hp => by ring)

theorem mass_le (R : ℕ) (ell : P → ℕ) (hell : ∀ p, 0 < ell p)
    {B : ℝ} (hB : 0 ≤ B) :
    mass (k := k) R ell B ≤ (R : ℝ) ^ 2 *
      Real.exp ((k : ℝ) * B * ∑ p, 1 / (ell p : ℝ) ^ 2) :=
  (mass_le_euler R ell hell hB).trans
    (mul_le_mul_of_nonneg_left (euler_le_exp ell hB) (sq_nonneg _))

theorem mass_le_of_small_tail (R : ℕ) (ell : P → ℕ) (hell : ∀ p, 0 < ell p)
    {B : ℝ} (hB : 0 ≤ B) (htail : (k : ℝ) * B * ∑ p, 1 / (ell p : ℝ) ^ 2 ≤ 1) :
    mass (k := k) R ell B ≤ Real.exp 1 * (R : ℝ) ^ 2 := by
  exact (mass_le R ell hell hB).trans
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htail) (sq_nonneg _)).trans_eq (mul_comm _ _))

end Erdos4.CutoffMass
