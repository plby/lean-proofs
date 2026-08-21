import ErdosProblems.Erdos239.External.Erdos67.LogElliott
import ErdosProblems.Erdos239.External.Erdos69.PrimeEstimates
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A finite Halász--Selberg mean bound for prime-avoidance functions

The equidistributed branch of Tao--Teräväinen's correlation theorem only
needs mean control for the nonnegative, completely multiplicative functions
which vanish on a finite packet of primes and equal one on all other primes.
For such functions the required endpoint is considerably more elementary
than the full complex Halász theorem: a one-level Selberg square gives

`sum_{n ≤ X} 1_{(n, ∏ p in P p) = 1}
    ≤ X / (1 + ∑ p in P, 1/p) + 2 * #P`.

This file proves that fully finite inequality and identifies its reciprocal
prime mass with the finite pretentious distance to the constant function.
There is no asymptotic or unproved analytic input in this module.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos69.HalaszMean

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

/-! ## Multiplicativity and the pretentious distance -/

theorem primeAvoidance_one (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    primeAvoidance P 1 = 1 := by
  rw [primeAvoidance, if_pos]
  intro p hp
  exact (hprime p hp).not_dvd_one

theorem primeAvoidance_mul (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    primeAvoidance P (m * n) = primeAvoidance P m * primeAvoidance P n := by
  have hiff :
      (∀ p ∈ P, ¬p ∣ m * n) ↔
        (∀ p ∈ P, ¬p ∣ m) ∧ (∀ p ∈ P, ¬p ∣ n) := by
    constructor
    · intro h
      constructor
      · intro p hp hpm
        exact h p hp (dvd_mul_of_dvd_left hpm n)
      · intro p hp hpn
        exact h p hp (dvd_mul_of_dvd_right hpn m)
    · rintro ⟨hm, hn⟩ p hp hpmn
      rcases (hprime p hp).dvd_mul.mp hpmn with hpm | hpn
      · exact hm p hp hpm
      · exact hn p hp hpn
  unfold primeAvoidance
  by_cases hm : ∀ p ∈ P, ¬p ∣ m
  · by_cases hn : ∀ p ∈ P, ¬p ∣ n
    · rw [if_pos (hiff.mpr ⟨hm, hn⟩), if_pos hm, if_pos hn]
      norm_num
    · have hprod : ¬∀ p ∈ P, ¬p ∣ m * n := fun h ↦ hn (hiff.mp h).2
      rw [if_neg hprod, if_pos hm, if_neg hn]
      norm_num
  · have hprod : ¬∀ p ∈ P, ¬p ∣ m * n := fun h ↦ hm (hiff.mp h).1
    rw [if_neg hprod, if_neg hm]
    norm_num

theorem primeAvoidanceComplex_isCompletelyMultiplicative
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Erdos67.IsCompletelyMultiplicativeOnPositive (primeAvoidanceComplex P) := by
  constructor
  · simp [primeAvoidanceComplex, primeAvoidance_one P hprime]
  · intro m n hm hn
    simp only [primeAvoidanceComplex, primeAvoidance_mul P hprime, Complex.ofReal_mul]

theorem primeAvoidance_at_prime (P : Finset ℕ)
    (hprime : ∀ q ∈ P, q.Prime) {p : ℕ} (hp : p.Prime) :
    primeAvoidance P p = if p ∈ P then 0 else 1 := by
  by_cases hpP : p ∈ P
  · rw [if_pos hpP, primeAvoidance, if_neg]
    push Not
    exact ⟨p, hpP, dvd_rfl⟩
  · rw [if_neg hpP, primeAvoidance, if_pos]
    intro q hqP hqp
    exact hpP ((Nat.prime_dvd_prime_iff_eq (hprime q hqP) hp).mp hqp ▸ hqP)

theorem pretentiousTerm_primeAvoidance_one (P : Finset ℕ)
    (hprime : ∀ q ∈ P, q.Prime) {p : ℕ} (hp : p.Prime) :
    Erdos67.pretentiousTerm (primeAvoidanceComplex P) (fun _ ↦ 1) p =
      if p ∈ P then (p : ℝ)⁻¹ else 0 := by
  rw [Erdos67.pretentiousTerm]
  rw [primeAvoidanceComplex, primeAvoidance_at_prime P hprime hp]
  by_cases hpP : p ∈ P <;> simp [hpP, one_div]

/-- For prime-avoidance functions, distance from the constant function is
exactly the reciprocal mass of the removed primes up to the cutoff. -/
theorem pretentiousDistSq_primeAvoidance_one (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (X : ℕ) :
    Erdos67.pretentiousDistSq (primeAvoidanceComplex P) (fun _ ↦ 1) X =
      reciprocalMass (P.filter fun p ↦ p ≤ X) := by
  rw [Erdos67.pretentiousDistSq, reciprocalMass]
  have hterms :
      (∑ p ∈ Erdos67.primesUpTo X,
        Erdos67.pretentiousTerm (primeAvoidanceComplex P) (fun _ ↦ 1) p) =
      ∑ p ∈ Erdos67.primesUpTo X,
        if p ∈ P then (p : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact pretentiousTerm_primeAvoidance_one P hprime
      (Erdos67.mem_primesUpTo.mp hp).1
  rw [hterms]
  calc
    (∑ p ∈ Erdos67.primesUpTo X, if p ∈ P then (p : ℝ)⁻¹ else 0) =
        ∑ p ∈ Erdos67.primesUpTo X ∩ P, (p : ℝ)⁻¹ := by
      rw [← Finset.sum_filter]
      congr 1
    _ = ∑ p ∈ P.filter (fun p ↦ p ≤ X), (p : ℝ)⁻¹ := by
      apply Finset.sum_congr
      · ext p
        simp only [Finset.mem_inter, Erdos67.mem_primesUpTo, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp, hpX⟩, hpP⟩
          exact ⟨hpP, hpX⟩
        · rintro ⟨hpP, hpX⟩
          exact ⟨⟨hprime p hpP, hpX⟩, hpP⟩
      · intro p hp
        rfl

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

theorem sum_linear_dvdIndicator (P : Finset ℕ) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, ∑ p ∈ P, dvdIndicator p n) =
      ∑ p ∈ P, ((X / p : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact sum_dvdIndicator_Ioc X p

theorem sum_quadratic_dvdIndicator (P : Finset ℕ) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, (∑ p ∈ P, dvdIndicator p n) ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P, ((X / Nat.lcm p q : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Finset.Ioc 0 X, (∑ p ∈ P, dvdIndicator p n) ^ 2) =
        ∑ n ∈ Finset.Ioc 0 X,
          ∑ p ∈ P, ∑ q ∈ P, dvdIndicator p n * dvdIndicator q n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = ∑ p ∈ P, ∑ q ∈ P,
        ∑ n ∈ Finset.Ioc 0 X, dvdIndicator p n * dvdIndicator q n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P, ∑ q ∈ P, ((X / Nat.lcm p q : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simp_rw [dvdIndicator_mul]
      exact sum_dvdIndicator_Ioc X (Nat.lcm p q)

theorem linear_floor_lower (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (X : ℕ) :
    (X : ℝ) * reciprocalMass P - P.card ≤
      ∑ p ∈ P, ((X / p : ℕ) : ℝ) := by
  calc
    (X : ℝ) * reciprocalMass P - P.card =
        ∑ p ∈ P, ((X : ℝ) / p - 1) := by
      rw [reciprocalMass, Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro p hp
        rw [div_eq_mul_inv]
      · simp
    _ ≤ ∑ p ∈ P, ((X / p : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact cast_div_lower X p (hprime p hp).pos

theorem quadratic_floor_upper (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (X : ℕ) :
    (∑ p ∈ P, ∑ q ∈ P, ((X / Nat.lcm p q : ℕ) : ℝ)) ≤
      (X : ℝ) * (reciprocalMass P ^ 2 + diagonalMass P) := by
  calc
    (∑ p ∈ P, ∑ q ∈ P, ((X / Nat.lcm p q : ℕ) : ℝ)) ≤
        ∑ p ∈ P, ∑ q ∈ P, (X : ℝ) / Nat.lcm p q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact cast_div_upper X (Nat.lcm p q)
    _ = (X : ℝ) *
        (∑ p ∈ P, ∑ q ∈ P, ((Nat.lcm p q : ℕ) : ℝ)⁻¹) := by
      simp_rw [div_eq_mul_inv, Finset.mul_sum]
    _ = (X : ℝ) * (reciprocalMass P ^ 2 + diagonalMass P) := by
      rw [sum_inv_lcm_eq_sq_add_diagonalMass P hprime]

theorem sum_selbergLinearWeight_sq (P : Finset ℕ) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, selbergLinearWeight P n ^ 2) =
      (X : ℝ) - 2 * selbergCoefficient P *
          (∑ p ∈ P, ((X / p : ℕ) : ℝ)) +
        selbergCoefficient P ^ 2 *
          (∑ p ∈ P, ∑ q ∈ P,
            ((X / Nat.lcm p q : ℕ) : ℝ)) := by
  let c := selbergCoefficient P
  let A : ℕ → ℝ := fun n ↦ ∑ p ∈ P, dvdIndicator p n
  calc
    (∑ n ∈ Finset.Ioc 0 X, selbergLinearWeight P n ^ 2) =
        ∑ n ∈ Finset.Ioc 0 X,
          (1 - 2 * c * A n + c ^ 2 * (A n) ^ 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [c, A, selbergLinearWeight]
      ring
    _ = (∑ n ∈ Finset.Ioc 0 X, (1 : ℝ)) -
          ∑ n ∈ Finset.Ioc 0 X, 2 * c * A n +
          ∑ n ∈ Finset.Ioc 0 X, c ^ 2 * (A n) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (X : ℝ) - 2 * c *
          (∑ n ∈ Finset.Ioc 0 X, A n) +
        c ^ 2 * (∑ n ∈ Finset.Ioc 0 X, (A n) ^ 2) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp
    _ = (X : ℝ) - 2 * selbergCoefficient P *
          (∑ p ∈ P, ((X / p : ℕ) : ℝ)) +
        selbergCoefficient P ^ 2 *
          (∑ p ∈ P, ∑ q ∈ P,
            ((X / Nat.lcm p q : ℕ) : ℝ)) := by
      dsimp [c, A]
      rw [sum_linear_dvdIndicator, sum_quadratic_dvdIndicator]

/-- The unoptimized one-level Selberg-square estimate. -/
theorem primeAvoidance_sum_le_selbergQuadratic (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, primeAvoidance P n) ≤
      (X : ℝ) *
          (1 - 2 * selbergCoefficient P * reciprocalMass P +
            selbergCoefficient P ^ 2 *
              (reciprocalMass P ^ 2 + diagonalMass P)) +
        2 * selbergCoefficient P * P.card := by
  have hdiag : 0 ≤ diagonalMass P := diagonalMass_nonneg P hprime
  have hc : 0 ≤ selbergCoefficient P := selbergCoefficient_nonneg P hdiag
  have hlinear := linear_floor_lower P hprime X
  have hquad := quadratic_floor_upper P hprime X
  calc
    (∑ n ∈ Finset.Ioc 0 X, primeAvoidance P n) ≤
        ∑ n ∈ Finset.Ioc 0 X, selbergLinearWeight P n ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact primeAvoidance_le_selbergLinearWeight_sq P n
    _ = (X : ℝ) - 2 * selbergCoefficient P *
          (∑ p ∈ P, ((X / p : ℕ) : ℝ)) +
        selbergCoefficient P ^ 2 *
          (∑ p ∈ P, ∑ q ∈ P,
            ((X / Nat.lcm p q : ℕ) : ℝ)) :=
      sum_selbergLinearWeight_sq P X
    _ ≤ (X : ℝ) - 2 * selbergCoefficient P *
          ((X : ℝ) * reciprocalMass P - P.card) +
        selbergCoefficient P ^ 2 *
          ((X : ℝ) * (reciprocalMass P ^ 2 + diagonalMass P)) := by
      have hcoef : 0 ≤ (2 : ℝ) * selbergCoefficient P :=
        mul_nonneg (by norm_num) hc
      have hlinmul :
          (2 * selbergCoefficient P) *
              ((X : ℝ) * reciprocalMass P - P.card) ≤
            (2 * selbergCoefficient P) *
              (∑ p ∈ P, ((X / p : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlinear hcoef
      have hneg := neg_le_neg hlinmul
      have hqmul := mul_le_mul_of_nonneg_left hquad
        (sq_nonneg (selbergCoefficient P))
      linarith
    _ = (X : ℝ) *
          (1 - 2 * selbergCoefficient P * reciprocalMass P +
            selbergCoefficient P ^ 2 *
              (reciprocalMass P ^ 2 + diagonalMass P)) +
        2 * selbergCoefficient P * P.card := by ring

theorem reciprocalMass_pos_of_nonempty (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) :
    0 < reciprocalMass P := by
  unfold reciprocalMass
  apply Finset.sum_pos
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact inv_pos.mpr hp0
  · exact hne

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

/-- Quantitative Halász--Selberg endpoint for a nonempty prime packet.

The error `2 * #P` is the complete finite endpoint error.  In the TT
specialization the packet endpoints are subpolynomial in `X`, while the
reciprocal mass is a fixed positive multiple of `log log X`; hence this is
the required power-of-logarithm mean saving. -/
theorem primeAvoidance_sum_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hmass : 0 < reciprocalMass P) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, primeAvoidance P n) ≤
      (X : ℝ) / (1 + reciprocalMass P) + 2 * P.card := by
  have hbase := primeAvoidance_sum_le_selbergQuadratic P hprime X
  rw [selbergQuadratic_eq_diagonal_div P hmass] at hbase
  have hdecay := diagonal_div_le_halasz_decay P hmass
  have hmain :
      (X : ℝ) * (diagonalMass P /
          (reciprocalMass P ^ 2 + diagonalMass P)) ≤
        (X : ℝ) * (1 / (1 + reciprocalMass P)) :=
    mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg X)
  have hc1 : selbergCoefficient P ≤ 1 :=
    selbergCoefficient_le_one P hmass
  have hcoef : (2 : ℝ) * selbergCoefficient P ≤ 2 := by
    linarith
  have herr : (2 : ℝ) * selbergCoefficient P * P.card ≤ 2 * P.card :=
    mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg P.card)
  calc
    (∑ n ∈ Finset.Ioc 0 X, primeAvoidance P n) ≤
        (X : ℝ) * (diagonalMass P /
            (reciprocalMass P ^ 2 + diagonalMass P)) +
          2 * selbergCoefficient P * P.card := hbase
    _ ≤ (X : ℝ) * (1 / (1 + reciprocalMass P)) + 2 * P.card :=
      add_le_add hmain herr
    _ = (X : ℝ) / (1 + reciprocalMass P) + 2 * P.card := by
      simp [div_eq_mul_inv]

theorem primeAvoidance_sum_le_of_nonempty (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, primeAvoidance P n) ≤
      (X : ℝ) / (1 + reciprocalMass P) + 2 * P.card :=
  primeAvoidance_sum_le P hprime
    (reciprocalMass_pos_of_nonempty P hprime hne) X

/-- Dyadic-interval form used in the correlation argument. -/
theorem primeAvoidance_dyadic_sum_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hmass : 0 < reciprocalMass P) (N : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), primeAvoidance P n) ≤
      ((2 * N : ℕ) : ℝ) / (1 + reciprocalMass P) + 2 * P.card := by
  have hsubset : Finset.Ioc N (2 * N) ⊆ Finset.Ioc 0 (2 * N) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨Nat.zero_lt_of_lt hn.1, hn.2⟩
  calc
    (∑ n ∈ Finset.Ioc N (2 * N), primeAvoidance P n) ≤
        ∑ n ∈ Finset.Ioc 0 (2 * N), primeAvoidance P n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn hnot
      exact primeAvoidance_nonneg P n
    _ ≤ ((2 * N : ℕ) : ℝ) / (1 + reciprocalMass P) + 2 * P.card :=
      primeAvoidance_sum_le P hprime hmass (2 * N)

theorem primeAvoidance_dyadic_normalized_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hmass : 0 < reciprocalMass P)
    {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N (2 * N), primeAvoidance P n) / (N : ℝ) ≤
      2 / (1 + reciprocalMass P) + (2 * P.card : ℝ) / N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hNreal]
  calc
    (∑ n ∈ Finset.Ioc N (2 * N), primeAvoidance P n) ≤
        ((2 * N : ℕ) : ℝ) / (1 + reciprocalMass P) + 2 * P.card :=
      primeAvoidance_dyadic_sum_le P hprime hmass N
    _ = (2 / (1 + reciprocalMass P) + (2 * P.card : ℝ) / N) * N := by
      norm_num [Nat.cast_mul]
      field_simp [ne_of_gt hNreal]

/-- A directly consumable error-budget form: reciprocal mass `A` and a
small endpoint ratio imply a small normalized dyadic mean. -/
theorem primeAvoidance_dyadic_normalized_le_of_mass
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {A ε : ℝ} (hA : 0 ≤ A) (hAmass : A ≤ reciprocalMass P)
    {N : ℕ} (hN : 0 < N) (hendpoint : (2 * P.card : ℝ) / N ≤ ε) :
    (∑ n ∈ Finset.Ioc N (2 * N), primeAvoidance P n) / (N : ℝ) ≤
      2 / (1 + A) + ε := by
  by_cases hne : P.Nonempty
  · have hmass : 0 < reciprocalMass P :=
      reciprocalMass_pos_of_nonempty P hprime hne
    have hbase := primeAvoidance_dyadic_normalized_le P hprime hmass hN
    have hdenA : 0 < 1 + A := by linarith
    have hdecay : 2 / (1 + reciprocalMass P) ≤ 2 / (1 + A) := by
      apply div_le_div_of_nonneg_left (by norm_num) hdenA
      linarith
    linarith
  · have hP : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst P
    have heps : 0 ≤ ε := by simpa using hendpoint
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hAupper : A ≤ 0 := by simpa [reciprocalMass] using hAmass
    have hsum :
        (∑ n ∈ Finset.Ioc N (2 * N), primeAvoidance ∅ n) = (N : ℝ) := by
      have hcard : (Finset.Ioc N (2 * N)).card = N := by
        simp
        omega
      rw [show (∑ n ∈ Finset.Ioc N (2 * N), primeAvoidance ∅ n) =
          ((Finset.Ioc N (2 * N)).card : ℝ) by simp [primeAvoidance], hcard]
    rw [hsum, div_self hNreal.ne']
    have hdenA : 0 < 1 + A := by linarith
    have : (1 : ℝ) ≤ 2 / (1 + A) := by
      rw [le_div_iff₀ hdenA]
      nlinarith [hAupper]
    linarith

/-! ## Mertens-window specialization -/

theorem reciprocalMass_primesIn (L U : ℕ) :
    reciprocalMass (Erdos69.PrimeEstimates.primesIn L U) =
      Erdos69.PrimeEstimates.reciprocalPrimeMass L U := by
  simp [reciprocalMass, Erdos69.PrimeEstimates.reciprocalPrimeMass,
    one_div]

/-- The explicit logarithmic-decay form obtained by feeding the repository's
Mertens estimate into the finite Selberg square. -/
theorem primeWindow_sum_le_of_mertens
    {C : ℝ}
    (hMertens : ∀ x : ℕ, 2 ≤ x →
      |Erdos69.PrimeEstimates.reciprocalPrimeSum x -
        Real.log (Real.log (x : ℝ))| ≤ C)
    {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U)
    (hpositive : 0 <
      Real.log (Real.log (U : ℝ)) -
        Real.log (Real.log (L : ℝ)) - 2 * C)
    (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X,
        primeAvoidance (Erdos69.PrimeEstimates.primesIn L U) n) ≤
      (X : ℝ) /
          (1 + (Real.log (Real.log (U : ℝ)) -
            Real.log (Real.log (L : ℝ)) - 2 * C)) +
        2 * (Erdos69.PrimeEstimates.primesIn L U).card := by
  let P := Erdos69.PrimeEstimates.primesIn L U
  let A := Real.log (Real.log (U : ℝ)) -
    Real.log (Real.log (L : ℝ)) - 2 * C
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Erdos69.PrimeEstimates.mem_primesIn.mp hp).2.2
  have hmassLower : A ≤ reciprocalMass P := by
    rw [reciprocalMass_primesIn]
    exact Erdos69.PrimeEstimates.log_log_diff_sub_two_mul_le_reciprocalPrimeMass
      hMertens hL hLU
  have hmass : 0 < reciprocalMass P := hpositive.trans_le hmassLower
  have hbase := primeAvoidance_sum_le P hprime hmass X
  have hdenA : 0 < 1 + A := by dsimp [A]; linarith
  have hdecay : 1 / (1 + reciprocalMass P) ≤ 1 / (1 + A) := by
    exact one_div_le_one_div_of_le hdenA (by linarith)
  have hmain :
      (X : ℝ) / (1 + reciprocalMass P) ≤ (X : ℝ) / (1 + A) := by
    calc
      (X : ℝ) / (1 + reciprocalMass P) =
          (X : ℝ) * (1 / (1 + reciprocalMass P)) := by ring
      _ ≤ (X : ℝ) * (1 / (1 + A)) :=
        mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg X)
      _ = (X : ℝ) / (1 + A) := by ring
  dsimp [P, A] at hbase hmain ⊢
  exact hbase.trans (add_le_add hmain le_rfl)

end

end Erdos69.HalaszMean
