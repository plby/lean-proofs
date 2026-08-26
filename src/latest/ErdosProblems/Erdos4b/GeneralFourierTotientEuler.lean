/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientIncidence

/-!
# Exact finite Euler identity with a totient denominator

The sum remains over the original squarefree divisor tuples with their
prime-local compatibility restrictions. The denominator is the totient
of their actual flat lcm.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance totientEulerDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

theorem totientDoubledFourierPrimeFactor_eq_polynomial
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) :
    totientDoubledFourierPrimeFactor edges companion s p =
      doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) ((p : ℝ) - 1)
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inl i) false))
          (primeFourierPower p (s (.inl i) true)))
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inr i) false))
          (primeFourierPower p (s (.inr i) true))) := by
  simp only [totientDoubledFourierPrimeFactor, doubledFourierPrimeNumerator,
    doubledFourierLocalPolynomial, Complex.ofReal_one, div_one, add_sub_cancel_left,
    Complex.ofReal_sub, Complex.ofReal_natCast]

theorem sum_reconstructed_totientDivisorFourierWeight_eq_eulerProduct
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ c : P → DoubledPrimeChoice ι,
      if ∀ p : P, DoubledPrimeChoiceAllowed (edges p) (companion p) (c p) then
        totientDoubledDivisorFourierWeight (doubledPrimeChoiceDivisor P c) s else 0) =
      ∏ p ∈ P, totientDoubledFourierPrimeFactor edges companion s p := by
  classical
  calc
    _ = ∑ c : P → DoubledPrimeChoice ι, ∏ p : P,
        doubledPrimeChoiceWeight (edges p) (companion p) ((p.val : ℝ) - 1)
          (fun i ↦ primeFourierPower p (s (.inl i) false))
          (fun i ↦ primeFourierPower p (s (.inl i) true))
          (fun i ↦ primeFourierPower p (s (.inr i) false))
          (fun i ↦ primeFourierPower p (s (.inr i) true)) (c p) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (prod_totient_doubledPrimeChoiceWeight_eq_divisorFourierWeight
        P hP edges companion c s).symm
    _ = ∏ p : P, totientDoubledFourierPrimeFactor edges companion s p := by
      rw [← Fintype.prod_sum]
      apply Finset.prod_congr rfl
      intro p hp
      rw [sum_doubledPrimeChoiceWeight, totientDoubledFourierPrimeFactor_eq_polynomial]
    _ = _ := Finset.prod_coe_sort P (fun p ↦ totientDoubledFourierPrimeFactor edges companion s p)

theorem sum_totientDoubledDivisorFourierWeight_eq_finiteEulerProduct
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p ∈ P, ∀ ij ∈ edges p, companion p = true)
    (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ d ∈ doubledCutoffDivisorTuples ι P,
      if DoubledDivisorPrimeCompatible P edges companion d then
        totientDoubledDivisorFourierWeight d s else 0) =
      ∏ p ∈ P, totientDoubledFourierPrimeFactor edges companion s p := by
  classical
  rw [sum_doubledCutoffDivisorTuples P hP]
  simp_rw [doubledDivisorPrimeCompatible_reconstructed P hP edges companion hedges]
  exact sum_reconstructed_totientDivisorFourierWeight_eq_eulerProduct P hP edges companion s

end

end Erdos4b
