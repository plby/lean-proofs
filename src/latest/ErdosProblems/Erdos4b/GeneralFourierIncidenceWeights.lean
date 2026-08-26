/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierIncidence

/-!
# Prime-local weights of reconstructed squarefree divisors

The Möbius signs, Fourier powers, and lcm denominator are factored using
the actual natural-number divisor reconstruction.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance incidenceWeightsDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

def primePairChoiceNumerator {ι : Type*} [Fintype ι]
    (c : Option (ι × Fin 3)) (W : ι → Bool → ℂ) : ℂ :=
  ∏ i, ∏ b, if primePairChoiceIncidence c i b then -W i b else 1

theorem primePairChoiceNumerator_none {ι : Type*} [Fintype ι] (W : ι → Bool → ℂ) :
    primePairChoiceNumerator none W = 1 := by
  simp [primePairChoiceNumerator, primePairChoiceIncidence]

theorem primePairChoiceNumerator_some {ι : Type*} [Fintype ι]
    (W : ι → Bool → ℂ) (i : ι) (r : Fin 3) :
    primePairChoiceNumerator (some (i, r)) W =
      primePairStateWeight (W i false) (W i true) r := by
  classical
  unfold primePairChoiceNumerator
  rw [Finset.prod_eq_single i]
  · rw [Fintype.prod_bool, primePairStateWeight_eq_signed_powers]
    simp [primePairChoiceIncidence, mul_comm]
  · intro j hj hji
    simp [primePairChoiceIncidence, Ne.symm hji]
  · simp

def doubledPrimeChoiceNumerator {ι : Type*} [Fintype ι]
    (c : DoubledPrimeChoice ι) (W : (ι ⊕ ι) → Bool → ℂ) : ℂ :=
  ∏ i, ∏ b, if doubledPrimeChoiceIncidence c i b then -W i b else 1

theorem doubledPrimeChoiceNumerator_eq_pair_product {ι : Type*} [Fintype ι]
    (c : DoubledPrimeChoice ι) (W : (ι ⊕ ι) → Bool → ℂ) :
    doubledPrimeChoiceNumerator c W =
      primePairChoiceNumerator ((doubledPrimeChoicePairEquiv ι c).1) (fun i ↦ W (.inl i)) *
        primePairChoiceNumerator ((doubledPrimeChoicePairEquiv ι c).2) (fun i ↦ W (.inr i)) := by
  rw [doubledPrimeChoiceNumerator, Fintype.prod_sum_type]
  rfl

def DoubledPrimeChoiceAllowed {ι : Type*}
    (edges : Finset (ι × ι)) (companion : Bool) : DoubledPrimeChoice ι → Prop
  | none => True
  | some (.inl _) => True
  | some (.inr (.inl _)) => companion = true
  | some (.inr (.inr (ij, _))) => ij ∈ edges

theorem doubledPrimeChoiceWeight_eq_incidence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : Finset (ι × ι)) (companion : Bool) (p : ℝ)
    (W : (ι ⊕ ι) → Bool → ℂ) (c : DoubledPrimeChoice ι) :
    doubledPrimeChoiceWeight edges companion p
        (fun i ↦ W (.inl i) false) (fun i ↦ W (.inl i) true)
        (fun i ↦ W (.inr i) false) (fun i ↦ W (.inr i) true) c =
      if DoubledPrimeChoiceAllowed edges companion c then
        doubledPrimeChoiceNumerator c W / (if c = none then 1 else (p : ℂ))
      else 0 := by
  rw [doubledPrimeChoiceNumerator_eq_pair_product]
  rcases c with _ | (⟨i, r⟩ | (⟨j, s⟩ | ⟨⟨i, j⟩, ⟨r, s⟩⟩))
  · simp [doubledPrimeChoiceWeight, DoubledPrimeChoiceAllowed,
      doubledPrimeChoicePairEquiv, primePairChoiceNumerator_none]
  · simp [doubledPrimeChoiceWeight, DoubledPrimeChoiceAllowed,
      doubledPrimeChoicePairEquiv, primePairChoiceNumerator_some, primePairChoiceNumerator_none]
  · cases companion <;> simp [doubledPrimeChoiceWeight, DoubledPrimeChoiceAllowed,
      doubledPrimeChoicePairEquiv, primePairChoiceNumerator_some, primePairChoiceNumerator_none]
  · simp [doubledPrimeChoiceWeight, DoubledPrimeChoiceAllowed,
      doubledPrimeChoicePairEquiv, primePairChoiceNumerator_some]

theorem moebius_fourier_doubledPrimeChoiceDivisor {ι : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : P → DoubledPrimeChoice ι)
    (i : ι ⊕ ι) (b : Bool) (s : ℂ) :
    (ArithmeticFunction.moebius (doubledPrimeChoiceDivisor P c i b) : ℂ) *
        primeFourierPower (doubledPrimeChoiceDivisor P c i b) s =
      ∏ p : P, if doubledPrimeChoiceIncidence (c p) i b then -primeFourierPower p s else 1 := by
  rw [doubledPrimeChoiceDivisor,
    moebius_mul_primeFourierPower_product _
      (fun p hp ↦ hP p (selectedCutoffPrimes_subset P c _ hp)),
    prod_selectedCutoffPrimes]

theorem prod_moebius_fourier_doubledPrimeChoiceDivisor
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (s : (ι ⊕ ι) → Bool → ℂ) :
    (∏ i, ∏ b, (ArithmeticFunction.moebius (doubledPrimeChoiceDivisor P c i b) : ℂ) *
      primeFourierPower (doubledPrimeChoiceDivisor P c i b) (s i b)) =
      ∏ p : P, doubledPrimeChoiceNumerator (c p) (fun i b ↦ primeFourierPower p (s i b)) := by
  simp_rw [moebius_fourier_doubledPrimeChoiceDivisor P hP]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_comm (s := (Finset.univ : Finset Bool))]
  rw [Finset.prod_comm]
  rfl

def doubledDivisorFourierWeight {ι : Type*} [Fintype ι]
    (d : (ι ⊕ ι) → Bool → ℕ) (s : (ι ⊕ ι) → Bool → ℂ) : ℂ :=
  (∏ i, ∏ b, (ArithmeticFunction.moebius (d i b) : ℂ) *
      primeFourierPower (d i b) (s i b)) /
    ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ)

theorem doubledDivisorFourierWeight_reconstructed
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (s : (ι ⊕ ι) → Bool → ℂ) :
    doubledDivisorFourierWeight (doubledPrimeChoiceDivisor P c) s =
      ∏ p : P, doubledPrimeChoiceNumerator (c p) (fun i b ↦ primeFourierPower p (s i b)) /
        (if c p = none then 1 else (p.val : ℂ)) := by
  rw [doubledDivisorFourierWeight, prod_moebius_fourier_doubledPrimeChoiceDivisor P hP,
    lcm_doubledPrimeChoiceDivisor P hP]
  push_cast
  rw [prod_selectedCutoffPrimes]
  simp only [ite_not]
  rw [Finset.prod_div_distrib]

theorem prod_doubledPrimeChoiceWeight_eq_divisorFourierWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (c : P → DoubledPrimeChoice ι) (s : (ι ⊕ ι) → Bool → ℂ) :
    (∏ p : P, doubledPrimeChoiceWeight (edges p) (companion p) p
      (fun i ↦ primeFourierPower p (s (.inl i) false))
      (fun i ↦ primeFourierPower p (s (.inl i) true))
      (fun i ↦ primeFourierPower p (s (.inr i) false))
      (fun i ↦ primeFourierPower p (s (.inr i) true)) (c p)) =
      if ∀ p : P, DoubledPrimeChoiceAllowed (edges p) (companion p) (c p) then
        doubledDivisorFourierWeight (doubledPrimeChoiceDivisor P c) s else 0 := by
  calc
    _ = ∏ p : P, if DoubledPrimeChoiceAllowed (edges p) (companion p) (c p) then
        doubledPrimeChoiceNumerator (c p) (fun i b ↦ primeFourierPower p (s i b)) /
          (if c p = none then 1 else (p.val : ℂ)) else 0 := by
      apply Finset.prod_congr rfl
      intro p hp
      exact doubledPrimeChoiceWeight_eq_incidence (edges p) (companion p) p
        (fun i b ↦ primeFourierPower p (s i b)) (c p)
    _ = _ := by rw [Fintype.prod_ite_zero, doubledDivisorFourierWeight_reconstructed P hP]

theorem sum_reconstructed_divisorFourierWeight_eq_eulerProduct
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ c : P → DoubledPrimeChoice ι,
      if ∀ p : P, DoubledPrimeChoiceAllowed (edges p) (companion p) (c p) then
        doubledDivisorFourierWeight (doubledPrimeChoiceDivisor P c) s else 0) =
      ∏ p ∈ P, doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) p
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inl i) false))
          (primeFourierPower p (s (.inl i) true)))
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inr i) false))
          (primeFourierPower p (s (.inr i) true))) := by
  classical
  calc
    _ = ∑ c : P → DoubledPrimeChoice ι, ∏ p : P,
        doubledPrimeChoiceWeight (edges p) (companion p) p
          (fun i ↦ primeFourierPower p (s (.inl i) false))
          (fun i ↦ primeFourierPower p (s (.inl i) true))
          (fun i ↦ primeFourierPower p (s (.inr i) false))
          (fun i ↦ primeFourierPower p (s (.inr i) true)) (c p) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (prod_doubledPrimeChoiceWeight_eq_divisorFourierWeight P hP edges companion c s).symm
    _ = _ := sum_prod_doubledPrimeChoiceWeight P edges companion
      (fun p i ↦ primeFourierPower p (s (.inl i) false))
      (fun p i ↦ primeFourierPower p (s (.inl i) true))
      (fun p i ↦ primeFourierPower p (s (.inr i) false))
      (fun p i ↦ primeFourierPower p (s (.inr i) true))

end

end Erdos4b
