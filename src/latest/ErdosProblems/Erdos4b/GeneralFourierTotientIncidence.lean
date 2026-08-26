/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientKernel
import ErdosProblems.Erdos4b.GeneralFourierFiniteEuler

/-!
# The literal totient denominator on reconstructed prime choices

The reconstructed flat lcm is the squarefree product of occupied primes.
Its totient is therefore exactly the product of `p - 1` on those primes.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance totientIncidenceDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

theorem totient_prod_distinct_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Nat.totient (∏ p ∈ P, p) = ∏ p ∈ P, (p - 1) := by
  classical
  rw [BoundedGaps.Maynard.totient_finsetProd_of_pairwise_coprime P (fun p ↦ p)
    (fun p hp q hq hpq ↦ (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)]
  exact Finset.prod_congr rfl (fun p hp ↦ Nat.totient_prime (hP p hp))

theorem totient_lcm_doubledPrimeChoiceDivisor
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) :
    (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
      (fun ib ↦ doubledPrimeChoiceDivisor P c ib.1 ib.2)) : ℂ) =
      ∏ p : P, if c p = none then 1 else ((p.val : ℂ) - 1) := by
  classical
  rw [lcm_doubledPrimeChoiceDivisor P hP,
    totient_prod_distinct_primes _ (fun p hp ↦ hP p (selectedCutoffPrimes_subset P c _ hp))]
  push_cast
  rw [prod_selectedCutoffPrimes]
  simp only [ite_not]
  apply Finset.prod_congr rfl
  intro p hp
  split_ifs
  · rfl
  · exact_mod_cast Nat.cast_sub (hP p p.property).one_lt.le

def totientDoubledDivisorFourierWeight {ι : Type*} [Fintype ι]
    (d : (ι ⊕ ι) → Bool → ℕ) (s : (ι ⊕ ι) → Bool → ℂ) : ℂ :=
  (∏ i, ∏ b, (ArithmeticFunction.moebius (d i b) : ℂ) *
    primeFourierPower (d i b) (s i b)) /
    (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) : ℕ)

theorem totientDoubledDivisorFourierWeight_reconstructed
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (s : (ι ⊕ ι) → Bool → ℂ) :
    totientDoubledDivisorFourierWeight (doubledPrimeChoiceDivisor P c) s =
      ∏ p : P, doubledPrimeChoiceNumerator (c p) (fun i b ↦ primeFourierPower p (s i b)) /
        (if c p = none then 1 else ((p.val : ℂ) - 1)) := by
  classical
  rw [totientDoubledDivisorFourierWeight,
    prod_moebius_fourier_doubledPrimeChoiceDivisor P hP,
    totient_lcm_doubledPrimeChoiceDivisor P hP, Finset.prod_div_distrib]

theorem prod_totient_doubledPrimeChoiceWeight_eq_divisorFourierWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (c : P → DoubledPrimeChoice ι) (s : (ι ⊕ ι) → Bool → ℂ) :
    (∏ p : P, doubledPrimeChoiceWeight (edges p) (companion p) ((p.val : ℝ) - 1)
      (fun i ↦ primeFourierPower p (s (.inl i) false))
      (fun i ↦ primeFourierPower p (s (.inl i) true))
      (fun i ↦ primeFourierPower p (s (.inr i) false))
      (fun i ↦ primeFourierPower p (s (.inr i) true)) (c p)) =
      if ∀ p : P, DoubledPrimeChoiceAllowed (edges p) (companion p) (c p) then
        totientDoubledDivisorFourierWeight (doubledPrimeChoiceDivisor P c) s else 0 := by
  classical
  calc
    _ = ∏ p : P, if DoubledPrimeChoiceAllowed (edges p) (companion p) (c p) then
        doubledPrimeChoiceNumerator (c p) (fun i b ↦ primeFourierPower p (s i b)) /
          (if c p = none then 1 else ((p.val : ℂ) - 1)) else 0 := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one] using
        doubledPrimeChoiceWeight_eq_incidence (edges p) (companion p) ((p.val : ℝ) - 1)
          (fun i b ↦ primeFourierPower p (s i b)) (c p)
    _ = _ := by rw [Fintype.prod_ite_zero, totientDoubledDivisorFourierWeight_reconstructed P hP]

end

end Erdos4b
