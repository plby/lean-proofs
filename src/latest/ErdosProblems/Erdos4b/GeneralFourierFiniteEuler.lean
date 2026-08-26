/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierIncidenceWeights
import ErdosProblems.Erdos4b.GeneralFourierReconstruction

/-!
# Exact finite Euler sum over squarefree divisor tuples

The sum is over natural-number divisor tuples, with explicit prime-local
companion and collision restrictions. Its value is the literal doubled
Fourier Euler polynomial. The next interface identifies these prime-local
restrictions with the affine CRT conditions.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance finiteEulerDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

def doubledPrimeChoicePresent {ι : Type*} (c : DoubledPrimeChoice ι) (i : ι ⊕ ι) : Prop :=
  ∃ b, doubledPrimeChoiceIncidence c i b

theorem doubledPrimeChoiceAllowed_iff_present {ι : Type*}
    (edges : Finset (ι × ι)) (companion : Bool)
    (hedges : ∀ ij ∈ edges, companion = true) (c : DoubledPrimeChoice ι) :
    DoubledPrimeChoiceAllowed edges companion c ↔
      (∀ j, doubledPrimeChoicePresent c (.inr j) → companion = true) ∧
        (∀ i j, doubledPrimeChoicePresent c (.inl i) →
          doubledPrimeChoicePresent c (.inr j) → (i, j) ∈ edges) := by
  simp only [doubledPrimeChoicePresent, doubledPrimeChoiceIncidence,
    primePairChoiceIncidence_exists]
  rcases c with _ | (⟨i, r⟩ | (⟨j, s⟩ | ⟨⟨i, j⟩, ⟨r, s⟩⟩))
  · simp [DoubledPrimeChoiceAllowed, doubledPrimeChoicePairEquiv]
  · simp [DoubledPrimeChoiceAllowed, doubledPrimeChoicePairEquiv]
  · simp [DoubledPrimeChoiceAllowed, doubledPrimeChoicePairEquiv]
  · simp only [DoubledPrimeChoiceAllowed, doubledPrimeChoicePairEquiv,
      Equiv.coe_fn_mk, Option.some.injEq, Prod.mk.injEq, exists_and_left,
      exists_eq', and_true]
    constructor
    · intro hij
      exact ⟨fun _ _ ↦ hedges (i, j) hij, fun a b ha hb ↦ by simpa [← ha, ← hb] using hij⟩
    · intro h
      exact h.2 i j rfl rfl

theorem prime_dvd_lcm_iff_or {p a b : ℕ} (hp : p.Prime) :
    p ∣ Nat.lcm a b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro h
    exact hp.dvd_mul.mp (h.trans (Nat.lcm_dvd_mul a b))
  · rintro (h | h)
    · exact h.trans (Nat.dvd_lcm_left a b)
    · exact h.trans (Nat.dvd_lcm_right a b)

theorem prime_dvd_reconstructed_lcm_iff_present {ι : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (p : P) (i : ι ⊕ ι) :
    p.val ∣ Nat.lcm (doubledPrimeChoiceDivisor P c i false)
        (doubledPrimeChoiceDivisor P c i true) ↔
      doubledPrimeChoicePresent (c p) i := by
  rw [prime_dvd_lcm_iff_or (hP p p.property),
    prime_dvd_doubledPrimeChoiceDivisor_iff P hP c i false p,
    prime_dvd_doubledPrimeChoiceDivisor_iff P hP c i true p]
  simp [doubledPrimeChoicePresent, Bool.exists_bool]

def DoubledDivisorPrimeCompatible {ι : Type*}
    (P : Finset ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (d : (ι ⊕ ι) → Bool → ℕ) : Prop :=
  ∀ p : P,
    (∀ j, p.val ∣ Nat.lcm (d (.inr j) false) (d (.inr j) true) → companion p = true) ∧
      (∀ i j, p.val ∣ Nat.lcm (d (.inl i) false) (d (.inl i) true) →
        p.val ∣ Nat.lcm (d (.inr j) false) (d (.inr j) true) → (i, j) ∈ edges p)

theorem doubledDivisorPrimeCompatible_reconstructed {ι : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p ∈ P, ∀ ij ∈ edges p, companion p = true)
    (c : P → DoubledPrimeChoice ι) :
    DoubledDivisorPrimeCompatible P edges companion (doubledPrimeChoiceDivisor P c) ↔
      ∀ p : P, DoubledPrimeChoiceAllowed (edges p) (companion p) (c p) := by
  unfold DoubledDivisorPrimeCompatible
  apply forall_congr'
  intro p
  rw [doubledPrimeChoiceAllowed_iff_present (edges p) (companion p) (hedges p p.property)]
  simp_rw [prime_dvd_reconstructed_lcm_iff_present P hP]

theorem sum_doubledDivisorFourierWeight_eq_finiteEulerProduct
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p ∈ P, ∀ ij ∈ edges p, companion p = true)
    (s : (ι ⊕ ι) → Bool → ℂ) :
    (∑ d ∈ doubledCutoffDivisorTuples ι P,
      if DoubledDivisorPrimeCompatible P edges companion d then
        doubledDivisorFourierWeight d s else 0) =
      ∏ p ∈ P, doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) p
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inl i) false))
          (primeFourierPower p (s (.inl i) true)))
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inr i) false))
          (primeFourierPower p (s (.inr i) true))) := by
  classical
  rw [sum_doubledCutoffDivisorTuples P hP]
  simp_rw [doubledDivisorPrimeCompatible_reconstructed P hP edges companion hedges]
  exact sum_reconstructed_divisorFourierWeight_eq_eulerProduct P hP edges companion s

end

end Erdos4b
