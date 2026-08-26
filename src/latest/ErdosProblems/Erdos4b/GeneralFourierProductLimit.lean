/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAbsoluteMajorant

/-!
# Convergence of the doubled Fourier Euler product

For a fixed positive real part of the Fourier exponents, the deviation
of each prime factor from one has a summable majorant. The finite prime
products therefore converge, with a bound independent of the cutoff.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem realPrimeEulerDecay_eq_rpow {p : ℝ} (hp : 0 < p) (σ : ℝ) :
    realPrimeEulerDecay σ p = p ^ (-σ) := by
  rw [Real.rpow_def_of_pos hp]
  unfold realPrimeEulerDecay
  congr 1
  ring

theorem summable_realPrimeEulerDecay {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes ↦ realPrimeEulerDecay σ p) := by
  have hnat : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr (by linarith)
  have hp := hnat.subtype Nat.Prime
  convert! hp using 1
  ext p
  exact realPrimeEulerDecay_eq_rpow (by exact_mod_cast p.property.pos) σ

def doubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) p
    (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inl i) false))
      (primeFourierPower p (s (.inl i) true)))
    (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inr i) false))
      (primeFourierPower p (s (.inr i) true)))

theorem norm_doubledFourierPrimeFactor_sub_one_le
    {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) (p : Nat.Primes) :
    ‖doubledFourierPrimeFactor edges companion s p - 1‖ ≤
      (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) * realPrimeEulerDecay σ p := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hρ1 := realPrimeEulerDecay_le_one (by linarith : 0 ≤ σ - 1) hp1.le
  calc
    _ ≤ (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) *
        realPrimeEulerDecay (σ - 1) p / p :=
      norm_doubledFourierLocalPolynomial_sub_one_le (edges p) (companion p)
        hp0 (realPrimeEulerDecay_pos _ _).le hρ1 _ _ _ _
        (fun i ↦ norm_primeFourierPower_le_decay hp1.le (hs (.inl i) false))
        (fun i ↦ norm_primeFourierPower_le_decay hp1.le (hs (.inl i) true))
        (fun i ↦ norm_primeFourierPower_le_decay hp1.le (hs (.inr i) false))
        (fun i ↦ norm_primeFourierPower_le_decay hp1.le (hs (.inr i) true))
    _ = _ := by rw [mul_div_assoc, realPrimeEulerDecay_sub_one_div hp0]

theorem summable_norm_doubledFourierPrimeFactor_sub_one
    {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) :
    Summable (fun p : Nat.Primes ↦ ‖doubledFourierPrimeFactor edges companion s p - 1‖) := by
  have hsum := (summable_realPrimeEulerDecay hσ).mul_left
    (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ)
  exact Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _)
    (norm_doubledFourierPrimeFactor_sub_one_le edges companion s hσ hs) hsum

theorem multipliable_doubledFourierPrimeFactor
    {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) :
    Multipliable (fun p : Nat.Primes ↦ doubledFourierPrimeFactor edges companion s p) := by
  have hsum := summable_norm_doubledFourierPrimeFactor_sub_one edges companion s hσ hs
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

theorem norm_prod_doubledFourierPrimeFactor_le_zeta
    {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) (Q : Finset Nat.Primes) :
    ‖∏ p ∈ Q, doubledFourierPrimeFactor edges companion s p‖ ≤
      ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  classical
  have hP : ∀ p ∈ Q.image Subtype.val, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  have h := norm_prod_doubledFourierPolynomial_le_zeta (Q.image Subtype.val) hP hσ edges companion
    (fun i ↦ s (.inl i) false) (fun i ↦ s (.inl i) true)
    (fun i ↦ s (.inr i) false) (fun i ↦ s (.inr i) true)
    (fun i ↦ hs (.inl i) false) (fun i ↦ hs (.inl i) true)
    (fun i ↦ hs (.inr i) false) (fun i ↦ hs (.inr i) true)
  change ‖∏ p ∈ Q.image Subtype.val, doubledFourierPrimeFactor edges companion s p‖ ≤ _ at h
  have heq := Finset.prod_image (s := Q) (g := fun p : Nat.Primes ↦ p.val)
    (f := doubledFourierPrimeFactor edges companion s)
    (fun p hp q hq h ↦ Subtype.ext h)
  exact (congrArg norm heq).symm.le.trans h

theorem norm_tprod_doubledFourierPrimeFactor_le_zeta
    {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) :
    ‖∏' p : Nat.Primes, doubledFourierPrimeFactor edges companion s p‖ ≤
      ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  apply le_of_tendsto (multipliable_doubledFourierPrimeFactor edges companion s hσ hs).hasProd.norm
  apply Filter.Eventually.of_forall
  intro Q
  simpa only [norm_prod] using norm_prod_doubledFourierPrimeFactor_le_zeta edges companion s hσ hs Q

end

end Erdos4b
