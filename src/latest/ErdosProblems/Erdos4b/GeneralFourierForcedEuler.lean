/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedDenominator
import ErdosProblems.Erdos4b.GeneralFourierForcedPrimeFactor
import ErdosProblems.Erdos4b.GeneralFourierTotientEuler

/-!
# Finite Fourier Euler identity with a prescribed prime-local state restriction

The prime-choice sum has the literal enlarged totient denominator.
Exactly one local factor is replaced, including its empty state.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def forcedDoubledDivisorFourierWeight {ι : Type*} [Fintype ι]
    (p : ℕ) (d : (ι ⊕ ι) → Bool → ℕ) (s : (ι ⊕ ι) → Bool → ℂ) : ℂ :=
  (∏ i, ∏ b, (ArithmeticFunction.moebius (d i b) : ℂ) * primeFourierPower (d i b) (s i b)) /
    (Nat.totient (Nat.lcm
      ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)

open Classical in
def oneForcedPrimeChoiceWeight {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (force : DoubledPrimeChoice ι → Prop) (p r : ℕ)
    (s : (ι ⊕ ι) → Bool → ℂ) (c : DoubledPrimeChoice ι) : ℂ :=
  if DoubledPrimeChoiceAllowed (edges r) (companion r) c ∧ (r = p → force c) then
    doubledPrimeChoiceNumerator c (fun i b ↦ primeFourierPower r (s i b)) /
      (if r = p ∨ c ≠ none then ((r : ℂ) - 1) else 1)
  else 0

open Classical in
theorem forcedDoubledDivisorFourierWeight_reconstructed
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (p : P) (c : P → DoubledPrimeChoice ι) (s : (ι ⊕ ι) → Bool → ℂ) :
    forcedDoubledDivisorFourierWeight p (doubledPrimeChoiceDivisor P c) s =
      ∏ r : P, doubledPrimeChoiceNumerator (c r) (fun i b ↦ primeFourierPower r (s i b)) /
        (if r.val = p.val ∨ c r ≠ none then ((r.val : ℂ) - 1) else 1) := by
  rw [forcedDoubledDivisorFourierWeight, prod_moebius_fourier_doubledPrimeChoiceDivisor P hP,
    totient_lcm_reconstructed_forced_prime_product P hP c p, Finset.prod_div_distrib]
  simp only [Subtype.val_inj]

open Classical in
theorem prod_oneForcedPrimeChoiceWeight_eq_divisorWeight
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (force : DoubledPrimeChoice ι → Prop) (p : P)
    (c : P → DoubledPrimeChoice ι) (s : (ι ⊕ ι) → Bool → ℂ) :
    (∏ r : P, oneForcedPrimeChoiceWeight edges companion force p r s (c r)) =
      if (∀ r : P, DoubledPrimeChoiceAllowed (edges r) (companion r) (c r)) ∧ force (c p) then
        forcedDoubledDivisorFourierWeight p (doubledPrimeChoiceDivisor P c) s else 0 := by
  have hcond : (∀ r : P, DoubledPrimeChoiceAllowed (edges r) (companion r) (c r) ∧
      (r.val = p.val → force (c r))) ↔
        (∀ r : P, DoubledPrimeChoiceAllowed (edges r) (companion r) (c r)) ∧ force (c p) := by
    constructor
    · intro hc
      exact ⟨fun r ↦ (hc r).1, (hc p).2 rfl⟩
    · rintro ⟨hc, hp⟩ r
      refine ⟨hc r, fun hr ↦ ?_⟩
      have heq : r = p := Subtype.ext hr
      simpa only [heq] using hp
  simp only [oneForcedPrimeChoiceWeight, Fintype.prod_ite_zero, hcond,
    forcedDoubledDivisorFourierWeight_reconstructed P hP p c s]

theorem sum_oneForcedPrimeChoiceWeight_at_forced
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (force : DoubledPrimeChoice ι → Prop) (p : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ c : DoubledPrimeChoice ι, oneForcedPrimeChoiceWeight edges companion force p p s c) =
      forcedTotientFourierPrimeFactor
        (fun c ↦ DoubledPrimeChoiceAllowed (edges p) (companion p) c ∧ force c) s p := by
  classical
  simp only [oneForcedPrimeChoiceWeight, true_implies, true_or, if_true,
    forcedTotientFourierPrimeFactor, forcedTotientLocalFactor,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]

theorem sum_oneForcedPrimeChoiceWeight_at_other
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (force : DoubledPrimeChoice ι → Prop) {p r : ℕ} (hr : r ≠ p)
    (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ c : DoubledPrimeChoice ι, oneForcedPrimeChoiceWeight edges companion force p r s c) =
      totientDoubledFourierPrimeFactor edges companion s r := by
  classical
  rw [totientDoubledFourierPrimeFactor_eq_polynomial, ← sum_doubledPrimeChoiceWeight]
  apply Finset.sum_congr rfl
  intro c hc
  rw [doubledPrimeChoiceWeight_eq_incidence (edges r) (companion r) ((r : ℝ) - 1)
    (fun i b ↦ primeFourierPower r (s i b)) c]
  simp only [oneForcedPrimeChoiceWeight, hr, false_implies, and_true, false_or, ite_not,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]

open Classical in
theorem sum_reconstructed_forcedDivisorFourierWeight_eq_eulerProduct
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (force : DoubledPrimeChoice ι → Prop) (p : P) (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ c : P → DoubledPrimeChoice ι,
      if (∀ r : P, DoubledPrimeChoiceAllowed (edges r) (companion r) (c r)) ∧ force (c p) then
        forcedDoubledDivisorFourierWeight p (doubledPrimeChoiceDivisor P c) s else 0) =
      ∏ r : P, if r = p then
        forcedTotientFourierPrimeFactor
          (fun c ↦ DoubledPrimeChoiceAllowed (edges p) (companion p) c ∧ force c) s p
        else totientDoubledFourierPrimeFactor edges companion s r := by
  simp_rw [← prod_oneForcedPrimeChoiceWeight_eq_divisorWeight P hP edges companion force p]
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro r hr
  by_cases heq : r = p
  · subst r
    rw [if_pos rfl, sum_oneForcedPrimeChoiceWeight_at_forced]
  · rw [if_neg heq, sum_oneForcedPrimeChoiceWeight_at_other edges companion force
      (fun hv ↦ heq (Subtype.ext hv))]

open Classical in
theorem sum_forcedDivisorFourierWeight_eq_finiteEulerProduct
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ r ∈ P, ∀ ij ∈ edges r, companion r = true)
    (p : P) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop) (force : DoubledPrimeChoice ι → Prop)
    (hR : ∀ c : P → DoubledPrimeChoice ι, R (doubledPrimeChoiceDivisor P c) ↔ force (c p))
    (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ d ∈ doubledCutoffDivisorTuples ι P,
      if DoubledDivisorPrimeCompatible P edges companion d ∧ R d then
        forcedDoubledDivisorFourierWeight p d s else 0) =
      ∏ r : P, if r = p then
        forcedTotientFourierPrimeFactor
          (fun c ↦ DoubledPrimeChoiceAllowed (edges p) (companion p) c ∧ force c) s p
        else totientDoubledFourierPrimeFactor edges companion s r := by
  rw [sum_doubledCutoffDivisorTuples P hP]
  simp_rw [doubledDivisorPrimeCompatible_reconstructed P hP edges companion hedges, hR]
  exact sum_reconstructed_forcedDivisorFourierWeight_eq_eulerProduct
    P hP edges companion force p s

end

end Erdos4b
