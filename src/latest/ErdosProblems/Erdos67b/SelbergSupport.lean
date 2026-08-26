import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Elementary Selberg-square support without correlation imports

The finite algebra and divisor-counting proofs here are reused from
`ErdosProblems.Erdos69.HalaszMean`.  They are kept in a separate namespace
because that module now imports an isolated copy of the Erdős 67
correlation definitions through Erdős 239; importing it together with the
canonical Erdős 67 modules creates duplicate declarations.  This support
module has only Mathlib dependencies and does not alter other tasks' files.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.SelbergSupport

noncomputable section

/-- The `0/1` completely multiplicative function which removes all
integers divisible by one of the primes in `P`. -/
def primeAvoidance (P : Finset ℕ) (n : ℕ) : ℝ :=
  if ∀ p ∈ P, ¬p ∣ n then 1 else 0

/-- Complex-valued version used by the pretentious-distance API. -/
def primeAvoidanceComplex (P : Finset ℕ) (n : ℕ) : ℂ :=
  (primeAvoidance P n : ℂ)

/-- Reciprocal-prime mass of a finite packet. -/
def reciprocalMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (p : ℝ)⁻¹

/-- The diagonal correction in the one-level Selberg square. -/
def diagonalMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ((p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ 2)

/-- Divisibility as a real-valued indicator. -/
def dvdIndicator (d n : ℕ) : ℝ :=
  if d ∣ n then 1 else 0

@[simp] theorem primeAvoidance_eq_one_iff {P : Finset ℕ} {n : ℕ} :
    primeAvoidance P n = 1 ↔ ∀ p ∈ P, ¬p ∣ n := by
  simp [primeAvoidance]

@[simp] theorem primeAvoidance_eq_zero_iff {P : Finset ℕ} {n : ℕ} :
    primeAvoidance P n = 0 ↔ ¬∀ p ∈ P, ¬p ∣ n := by
  simp [primeAvoidance]

theorem primeAvoidance_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ primeAvoidance P n := by
  unfold primeAvoidance
  split <;> norm_num

theorem primeAvoidance_le_one (P : Finset ℕ) (n : ℕ) :
    primeAvoidance P n ≤ 1 := by
  unfold primeAvoidance
  split <;> norm_num

theorem abs_primeAvoidance_le_one (P : Finset ℕ) (n : ℕ) :
    |primeAvoidance P n| ≤ 1 := by
  rw [abs_of_nonneg (primeAvoidance_nonneg P n)]
  exact primeAvoidance_le_one P n

theorem norm_primeAvoidanceComplex_le_one (P : Finset ℕ) (n : ℕ) :
    ‖primeAvoidanceComplex P n‖ ≤ 1 := by
  rw [primeAvoidanceComplex, Complex.norm_real, Real.norm_eq_abs]
  exact abs_primeAvoidance_le_one P n

theorem reciprocalMass_nonneg (P : Finset ℕ) :
    0 ≤ reciprocalMass P := by
  unfold reciprocalMass
  positivity

theorem diagonalMass_nonneg (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    0 ≤ diagonalMass P := by
  unfold diagonalMass
  apply Finset.sum_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := (inv_nonneg.mpr hp0.le)
  have hinv1 : (p : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      (one_div_le_one_div_of_le zero_lt_one hp1)
  nlinarith [mul_nonneg hinv0 (sub_nonneg.mpr hinv1)]

/-- For a prime packet, the diagonal correction is at most its reciprocal
mass. -/
theorem diagonalMass_le_reciprocalMass (P : Finset ℕ) :
    diagonalMass P ≤ reciprocalMass P := by
  unfold diagonalMass reciprocalMass
  apply Finset.sum_le_sum
  intro p hp
  exact sub_le_self _ (sq_nonneg ((p : ℝ)⁻¹))

/-- The square of the reciprocal mass dominates the sum of the squared
reciprocals. -/
theorem sum_inv_sq_le_reciprocalMass_sq (P : Finset ℕ) :
    (∑ p ∈ P, ((p : ℝ)⁻¹) ^ 2) ≤ reciprocalMass P ^ 2 := by
  unfold reciprocalMass
  have hnonneg : ∀ p ∈ P, 0 ≤ (p : ℝ)⁻¹ := by
    intro p hp
    positivity
  exact Finset.sum_sq_le_sq_sum_of_nonneg hnonneg

/-- Consequently the quadratic denominator is at least the reciprocal
mass. -/
theorem reciprocalMass_le_sq_add_diagonalMass (P : Finset ℕ) :
    reciprocalMass P ≤ reciprocalMass P ^ 2 + diagonalMass P := by
  have hsquare := sum_inv_sq_le_reciprocalMass_sq P
  rw [reciprocalMass] at hsquare
  rw [diagonalMass, Finset.sum_sub_distrib, reciprocalMass]
  linarith

/-- The Selberg coefficient is between zero and one. -/
def selbergCoefficient (P : Finset ℕ) : ℝ :=
  reciprocalMass P / (reciprocalMass P ^ 2 + diagonalMass P)

theorem selbergCoefficient_nonneg (P : Finset ℕ)
    (hdiag : 0 ≤ diagonalMass P) :
    0 ≤ selbergCoefficient P := by
  unfold selbergCoefficient
  exact div_nonneg (reciprocalMass_nonneg P)
    (add_nonneg (sq_nonneg _) hdiag)

theorem selbergCoefficient_le_one (P : Finset ℕ)
    (hmass : 0 < reciprocalMass P) :
    selbergCoefficient P ≤ 1 := by
  unfold selbergCoefficient
  have hden : 0 < reciprocalMass P ^ 2 + diagonalMass P :=
    lt_of_lt_of_le hmass (reciprocalMass_le_sq_add_diagonalMass P)
  rw [div_le_one hden]
  exact reciprocalMass_le_sq_add_diagonalMass P

/-- The linear Selberg weight whose square majorizes prime avoidance. -/
def selbergLinearWeight (P : Finset ℕ) (n : ℕ) : ℝ :=
  1 - selbergCoefficient P * ∑ p ∈ P, dvdIndicator p n

theorem primeAvoidance_le_selbergLinearWeight_sq (P : Finset ℕ) (n : ℕ) :
    primeAvoidance P n ≤ selbergLinearWeight P n ^ 2 := by
  by_cases h : ∀ p ∈ P, ¬p ∣ n
  · have hind : (∑ p ∈ P, dvdIndicator p n) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [dvdIndicator, h p hp]
    rw [primeAvoidance, if_pos h, selbergLinearWeight, hind]
    norm_num
  · rw [primeAvoidance, if_neg h]
    exact sq_nonneg _


/-! ## Exact finite divisor averages -/

theorem sum_dvdIndicator_Ioc (X d : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, dvdIndicator d n) = ((X / d : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Finset.Ioc 0 X, dvdIndicator d n) =
        ((Finset.Ioc 0 X).filter (fun n ↦ d ∣ n)).card := by
      simp only [dvdIndicator, Finset.sum_boole]
    _ = ((X / d : ℕ) : ℝ) := by
      norm_cast
      exact Nat.Ioc_filter_dvd_card_eq_div X d

theorem dvdIndicator_mul (a b n : ℕ) :
    dvdIndicator a n * dvdIndicator b n = dvdIndicator (Nat.lcm a b) n := by
  simp only [dvdIndicator, Nat.lcm_dvd_iff]
  by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;> simp [ha, hb]

theorem cast_div_lower (X d : ℕ) (hd : 0 < d) :
    (X : ℝ) / d - 1 ≤ ((X / d : ℕ) : ℝ) := by
  have hnat : X < (X / d + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (X / d))
  have hreal : (X : ℝ) < (((X / d : ℕ) : ℝ) + 1) * d := by
    exact_mod_cast hnat
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv : (X : ℝ) / d < ((X / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdreal).2
    simpa [mul_comm] using hreal
  linarith

theorem cast_div_upper (X d : ℕ) :
    ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := by
  exact Nat.cast_div_le

theorem inv_lcm_eq_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ((Nat.lcm p q : ℕ) : ℝ)⁻¹ =
      (p : ℝ)⁻¹ * (q : ℝ)⁻¹ +
        if p = q then (p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ 2 else 0 := by
  by_cases hpq : p = q
  · subst q
    simp only [Nat.lcm_self, if_pos, pow_two]
    ring
  · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    rw [if_neg hpq, hcop.lcm_eq_mul]
    push_cast
    rw [mul_inv_rev]
    ring

theorem sum_inv_lcm_eq_sq_add_diagonalMass (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, ∑ q ∈ P, ((Nat.lcm p q : ℕ) : ℝ)⁻¹) =
      reciprocalMass P ^ 2 + diagonalMass P := by
  calc
    (∑ p ∈ P, ∑ q ∈ P, ((Nat.lcm p q : ℕ) : ℝ)⁻¹) =
        ∑ p ∈ P, ∑ q ∈ P,
          ((p : ℝ)⁻¹ * (q : ℝ)⁻¹ +
            if p = q then (p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro p hpP
      apply Finset.sum_congr rfl
      intro q hqP
      exact inv_lcm_eq_of_primes (hprime p hpP) (hprime q hqP)
    _ = (∑ p ∈ P, (p : ℝ)⁻¹) ^ 2 +
        ∑ p ∈ P, ((p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ 2) := by
      simp_rw [Finset.sum_add_distrib]
      rw [show (∑ p ∈ P, ∑ q ∈ P, (p : ℝ)⁻¹ * (q : ℝ)⁻¹) =
          (∑ p ∈ P, (p : ℝ)⁻¹) ^ 2 by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, pow_two]]
      congr 1
      apply Finset.sum_congr rfl
      intro p hpP
      simp [hpP]
    _ = reciprocalMass P ^ 2 + diagonalMass P := by
      rfl


theorem selbergQuadratic_eq_diagonal_div (P : Finset ℕ)
    (hmass : 0 < reciprocalMass P) :
    1 - 2 * selbergCoefficient P * reciprocalMass P +
        selbergCoefficient P ^ 2 *
          (reciprocalMass P ^ 2 + diagonalMass P) =
      diagonalMass P /
        (reciprocalMass P ^ 2 + diagonalMass P) := by
  have hden : 0 < reciprocalMass P ^ 2 + diagonalMass P :=
    lt_of_lt_of_le hmass (reciprocalMass_le_sq_add_diagonalMass P)
  unfold selbergCoefficient
  field_simp [ne_of_gt hden]
  ring

theorem diagonal_div_le_halasz_decay (P : Finset ℕ)
    (hmass : 0 < reciprocalMass P) :
    diagonalMass P /
        (reciprocalMass P ^ 2 + diagonalMass P) ≤
      1 / (1 + reciprocalMass P) := by
  have hden : 0 < reciprocalMass P ^ 2 + diagonalMass P :=
    lt_of_lt_of_le hmass (reciprocalMass_le_sq_add_diagonalMass P)
  have hone : 0 < 1 + reciprocalMass P := by linarith
  rw [div_le_div_iff₀ hden hone]
  have hdiag_le := diagonalMass_le_reciprocalMass P
  have hmul : diagonalMass P * reciprocalMass P ≤
      reciprocalMass P * reciprocalMass P :=
    mul_le_mul_of_nonneg_right hdiag_le (reciprocalMass_nonneg P)
  nlinarith


end

end Erdos67b.SelbergSupport
