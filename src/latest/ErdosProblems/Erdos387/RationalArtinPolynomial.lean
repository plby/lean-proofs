/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalArtinCancellation
import Mathlib.Algebra.Polynomial.Reverse

/-!
# The rational Artin polynomial and its degree bound

The coefficient of degree `n` is the total rational Euler weight of all
monic degree-`n` polynomials.  The probe-line cancellation proves that these
coefficients vanish from degree `2 * |support|` onward, so the generating
series is represented by a literal polynomial of degree strictly less than
that cutoff.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalWeil

/-- Total Euler weight of the monic polynomials of degree `n`, parametrized
by their lower coefficient vectors. -/
noncomputable def monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (n : ℕ) : ℂ :=
  ∑ c : Fin n → ZMod p, polynomialWeight coeff (monicPolynomial n c)

/-- The finite rational Artin polynomial. -/
noncomputable def artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) : ℂ[X] :=
  ∑ n ∈ Finset.range (2 * (InverseRational.poleSupport coeff).card),
    monomial n (monicWeightSum coeff n)

theorem coeff_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (n : ℕ) :
    (artinLPolynomial coeff).coeff n =
      if n < 2 * (InverseRational.poleSupport coeff).card then
        monicWeightSum coeff n
      else 0 := by
  classical
  rw [artinLPolynomial, finsetSum_coeff]
  by_cases hn : n < 2 * (InverseRational.poleSupport coeff).card
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      rw [coeff_monomial]
      simp only [if_neg hmn]
    · simp [hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    rw [coeff_monomial]
    have hmn : m ≠ n := by
      intro h
      subst m
      exact hn (Finset.mem_range.mp hm)
    simp only [if_neg hmn]

/-- Under the nonempty-support hypothesis, every coefficient of the finite
Artin polynomial is the unrestricted monic weight sum. -/
theorem coeff_artinLPolynomial_eq_monicWeightSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) (n : ℕ) :
    (artinLPolynomial coeff).coeff n = monicWeightSum coeff n := by
  rw [coeff_artinLPolynomial]
  split_ifs with hn
  · rfl
  · symm
    unfold monicWeightSum
    exact sum_polynomialWeight_monicPolynomial_eq_zero coeff
      (Nat.le_of_not_gt hn) hne

theorem monicPolynomial_zero_eq_one
    {K : Type*} [Field K] (c : Fin 0 → K) :
    monicPolynomial 0 c = 1 := by
  rw [monicPolynomial]
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  simp [lowerPolynomial]

/-- The constant monic weight sum equals one. -/
theorem monicWeightSum_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) :
    monicWeightSum coeff 0 = 1 := by
  classical
  rw [monicWeightSum]
  simp only [monicPolynomial_zero_eq_one]
  have havoid : AvoidsPoleSupport coeff (1 : (ZMod p)[X]) := by
    intro r hr
    simp
  rw [show polynomialWeight coeff (1 : (ZMod p)[X]) = 1 by
    rw [polynomialWeight, if_pos havoid]
    simp [logarithmicDerivativePhase]]
  simp

/-- A nonempty pole support makes the Artin polynomial have constant
coefficient one. -/
theorem coeff_zero_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff).coeff 0 = 1 := by
  rw [coeff_artinLPolynomial_eq_monicWeightSum coeff hne,
    monicWeightSum_zero]

theorem artinLPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    artinLPolynomial coeff ≠ 0 := by
  intro hzero
  have := coeff_zero_artinLPolynomial coeff hne
  rw [hzero, coeff_zero] at this
  exact zero_ne_one this

/-- The rational Artin polynomial has degree strictly less than twice the
number of supported poles. -/
theorem natDegree_artinLPolynomial_lt
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff).natDegree <
      2 * (InverseRational.poleSupport coeff).card := by
  have hcard : 0 < (InverseRational.poleSupport coeff).card :=
    Finset.card_pos.mpr hne
  rw [Nat.lt_iff_le_pred (by omega :
    0 < 2 * (InverseRational.poleSupport coeff).card)]
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_artinLPolynomial, if_neg]
  omega

end RationalWeil

end Erdos387
