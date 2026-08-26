/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientProduct
import ErdosProblems.Erdos4b.GeneralFourierPresievedProduct

/-!
# Totient-denominator Fourier kernels

The exact local numerator is bounded by the number of nonempty prime
states. The full totient kernel factors into the already treated kernel
and a uniformly negligible product correction.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

def doubledFourierPrimeNumerator {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) 1
    (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inl i) false))
      (primeFourierPower p (s (.inl i) true)))
    (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inr i) false))
      (primeFourierPower p (s (.inr i) true))) - 1

def totientDoubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  1 + doubledFourierPrimeNumerator edges companion s p / ((p : ℝ) - 1)

def roughTotientDoubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  if w < p then totientDoubledFourierPrimeFactor edges companion s p else 1

theorem doubledFourierPrimeFactor_eq_one_add_numerator_div
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) :
    doubledFourierPrimeFactor edges companion s p =
      1 + doubledFourierPrimeNumerator edges companion s p / (p : ℂ) := by
  simp only [doubledFourierPrimeFactor, doubledFourierPrimeNumerator,
    doubledFourierLocalPolynomial, Complex.ofReal_one, div_one, add_sub_cancel_left,
    Complex.ofReal_natCast]

theorem norm_doubledFourierPrimeNumerator_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (hs : ∀ i b, 0 ≤ (s i b).re) (p : Nat.Primes) :
    ‖doubledFourierPrimeNumerator edges companion s p‖ ≤
      Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  simpa only [doubledFourierPrimeNumerator, mul_one, div_one] using
    norm_doubledFourierLocalPolynomial_sub_one_le
    (edges p) (companion p) (p := 1) (ρ := 1) (by norm_num) (by norm_num) le_rfl
    (fun i ↦ primeFourierPower p (s (.inl i) false))
    (fun i ↦ primeFourierPower p (s (.inl i) true))
    (fun i ↦ primeFourierPower p (s (.inr i) false))
    (fun i ↦ primeFourierPower p (s (.inr i) true))
    (fun i ↦ norm_primeFourierPower_le_one hp (hs _ _))
    (fun i ↦ norm_primeFourierPower_le_one hp (hs _ _))
    (fun i ↦ norm_primeFourierPower_le_one hp (hs _ _))
    (fun i ↦ norm_primeFourierPower_le_one hp (hs _ _))

theorem roughTotientDoubledFourierPrimeFactor_eq_correction_mul
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {w : ℕ}
    (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (hs : ∀ i b, 0 ≤ (s i b).re) (p : Nat.Primes) :
    roughTotientDoubledFourierPrimeFactor w edges companion s p =
      roughTotientFourierCorrection w (doubledFourierPrimeNumerator edges companion s) p *
        selectedDoubledFourierPrimeFactor (fun p ↦ decide (w < p)) edges companion s p := by
  by_cases hwp : w < p.val
  · have hhalf := half_le_norm_one_add_div_of_norm_le (p := (p : ℝ))
      (by exact_mod_cast p.property.pos) (hw.trans (by exact_mod_cast hwp.le))
      (norm_doubledFourierPrimeNumerator_le edges companion s hs p)
    have hne : 1 + doubledFourierPrimeNumerator edges companion s p / (p : ℂ) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hhalf)
    simp only [roughTotientDoubledFourierPrimeFactor, roughTotientFourierCorrection,
      selectedDoubledFourierPrimeFactor, decide_eq_true_eq, if_pos hwp]
    rw [doubledFourierPrimeFactor_eq_one_add_numerator_div]
    unfold totientDoubledFourierPrimeFactor totientFourierLocalCorrection
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_natCast]
    exact (div_mul_cancel₀ _ hne).symm
  · simp only [roughTotientDoubledFourierPrimeFactor, roughTotientFourierCorrection,
      selectedDoubledFourierPrimeFactor, decide_eq_true_eq, if_neg hwp, mul_one]

theorem hasProd_roughTotientDoubledFourierPrimeFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {w : ℕ} {σ : ℝ}
    (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (hσ : 1 < σ) (hs : ∀ i b, σ - 1 ≤ (s i b).re) :
    HasProd (fun p : Nat.Primes ↦ roughTotientDoubledFourierPrimeFactor w edges companion s p)
      ((∏' p : Nat.Primes,
          roughTotientFourierCorrection w (doubledFourierPrimeNumerator edges companion s) p) *
        ∏' p : Nat.Primes,
          selectedDoubledFourierPrimeFactor (fun p ↦ decide (w < p)) edges companion s p) := by
  have hs0 : ∀ i b, 0 ≤ (s i b).re := fun i b ↦ (by linarith : 0 ≤ σ - 1).trans (hs i b)
  have hC := multipliable_roughTotientFourierCorrection
    (doubledFourierPrimeNumerator edges companion s) (Nat.cast_nonneg _) hw
    (fun p hp ↦ norm_doubledFourierPrimeNumerator_le edges companion s hs0 p)
  have hK := multipliable_selectedDoubledFourierPrimeFactor
    (fun p ↦ decide (w < p)) edges companion s hσ hs
  convert! hC.hasProd.mul hK.hasProd using 1
  ext p
  exact roughTotientDoubledFourierPrimeFactor_eq_correction_mul edges companion s hw hs0 p

theorem norm_tprod_totientDoubledFourierCorrection_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {w : ℕ} (hw0 : 0 < w)
    (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (hs : ∀ i b, 0 ≤ (s i b).re) :
    ‖(∏' p : Nat.Primes,
        roughTotientFourierCorrection w (doubledFourierPrimeNumerator edges companion s) p) - 1‖ ≤
      Real.exp (8 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) / w) - 1 :=
  norm_tprod_roughTotientFourierCorrection_sub_one_le
    (doubledFourierPrimeNumerator edges companion s) (Nat.cast_nonneg _) hw0 hw
    (fun p _hp ↦ norm_doubledFourierPrimeNumerator_le edges companion s hs p)

end

end Erdos4b
