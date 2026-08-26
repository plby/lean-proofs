/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierDoubledComparison
import ErdosProblems.Erdos4b.GeneralFourierProductLimit

/-!
# Relative comparison with the singular and zeta reference factors

Exceptional first-order terms remain in the singular factor. The
relative error consists of a reciprocal-square term and an explicit
exceptional-prime perturbation, suitable for finite-product estimates.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def doubledFourierReferenceFactor {ι : Type*} [Fintype ι]
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  ∏ i, selbergPairZetaFactor p (primeFourierPower p (s i false)) (primeFourierPower p (s i true))

def doubledFourierSingularFactor {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) : ℂ :=
  (1 - ((Fintype.card (ι ⊕ ι) : ℂ) -
      doubledFourierExceptionalCount Finset.univ (edges p) (companion p)) / p) /
    (1 - 1 / (p : ℂ)) ^ Fintype.card (ι ⊕ ι)

def doubledFourierRelativeFactor {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  doubledFourierPrimeFactor edges companion s p /
    (doubledFourierReferenceFactor s p * doubledFourierSingularFactor edges companion p)

def fourierPairComparisonConstant (N : ℕ) : ℝ :=
  4 * N * (pairProductErrorConstant N + N) + 6 * pairProductErrorConstant N

def doubledFourierExceptionalCost {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) : ℝ :=
  (if companion p then 0 else (Fintype.card ι : ℝ)) + 4 * (edges p).card

theorem univ_disjSum_univ_eq (ι : Type*) [Fintype ι] :
    (Finset.univ : Finset ι).disjSum Finset.univ = (Finset.univ : Finset (ι ⊕ ι)) := by
  ext i
  cases i <;> simp

theorem half_le_norm_doubledFourierSingularFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {p : ℕ} (hp : 2 ≤ (p : ℝ)) (hcard : 4 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p)
    (hedgeCard : (edges p).card ≤ Fintype.card ι) :
    (1 / 2 : ℝ) ≤ ‖doubledFourierSingularFactor edges companion p‖ := by
  have hcount : doubledFourierExceptionalCount Finset.univ (edges p) (companion p) ≤
      Fintype.card (ι ⊕ ι) := by
    simpa only [univ_disjSum_univ_eq, Finset.card_univ] using
      doubledFourierExceptionalCount_le_double_card Finset.univ (edges p) (companion p)
        (by simpa only [Finset.card_univ] using hedgeCard)
  have hD : ‖(doubledFourierExceptionalCount Finset.univ (edges p) (companion p) : ℂ)‖ ≤
      (Fintype.card (ι ⊕ ι) : ℝ) := by
    simp only [Complex.norm_natCast]
    exact_mod_cast hcount
  exact half_le_norm_zeroExponentSingularFactor _ hp hcard hD

theorem doubledFourierReferenceFactor_ne_zero {ι : Type*} [Fintype ι]
    (s : (ι ⊕ ι) → Bool → ℂ) {p : ℕ} (hp : 2 ≤ (p : ℝ))
    (hRe : ∀ i b, 0 ≤ (s i b).re) : doubledFourierReferenceFactor s p ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact selbergPairZetaFactor_ne_zero hp
    (norm_primeFourierPower_le_one (by linarith) (hRe i false))
    (norm_primeFourierPower_le_one (by linarith) (hRe i true))

theorem doubledFourierPrimeFactor_eq_relative_mul
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {p : ℕ} (hp : 2 ≤ (p : ℝ))
    (hcard : 4 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p)
    (hedgeCard : (edges p).card ≤ Fintype.card ι) (hRe : ∀ i b, 0 ≤ (s i b).re) :
    doubledFourierPrimeFactor edges companion s p =
      doubledFourierRelativeFactor edges companion s p *
        (doubledFourierReferenceFactor s p * doubledFourierSingularFactor edges companion p) := by
  have hS : doubledFourierSingularFactor edges companion p ≠ 0 := by
    have h := half_le_norm_doubledFourierSingularFactor edges companion hp hcard hedgeCard
    intro hz
    rw [hz, norm_zero] at h
    norm_num at h
  exact (div_mul_cancel₀ _ (mul_ne_zero (doubledFourierReferenceFactor_ne_zero s hp hRe) hS)).symm

theorem norm_doubledFourierRelativeFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {p : ℕ} {σ : ℝ} (hp : 2 ≤ (p : ℝ))
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p)
    (hedgeCard : (edges p).card ≤ Fintype.card ι)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    ‖doubledFourierRelativeFactor edges companion s p - 1‖ ≤
      2 * (12 : ℝ) ^ Fintype.card (ι ⊕ ι) *
        (fourierPairComparisonConstant (Fintype.card (ι ⊕ ι)) / (p : ℝ) ^ 2 +
          doubledFourierExceptionalCost edges companion p * (2 * σ * Real.log p) / p) := by
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hfour : 4 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p := by
    have hn : (0 : ℝ) ≤ Fintype.card (ι ⊕ ι) := Nat.cast_nonneg _
    linarith
  have hbase := norm_doubledFourierLocalPolynomial_div_reference_sub_singular_le
    (Finset.univ : Finset ι) (edges p) (companion p)
    (fun i ↦ primeFourierPower p (s i false)) (fun i ↦ primeFourierPower p (s i true)) hp
    (by simpa only [univ_disjSum_univ_eq, Finset.card_univ] using hcard)
    (fun i hi ↦ norm_primeFourierPower_le_one hp1 (hRe i false))
    (fun i hi ↦ norm_primeFourierPower_le_one hp1 (hRe i true))
    (fun i hi ↦ norm_selbergPairPolynomial_primeFourierPowers_add_one_le hp1
      (hRe (.inl i) false) (hRe (.inl i) true) (hNorm (.inl i)))
    (fun i hi ↦ norm_selbergPairPolynomial_primeFourierPowers_add_one_le hp1
      (hRe (.inr i) false) (hRe (.inr i) true) (hNorm (.inr i)))
    (fun ij hij ↦ ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (by simpa only [Finset.card_univ] using hedgeCard)
  have hbound : ‖doubledFourierPrimeFactor edges companion s p /
        doubledFourierReferenceFactor s p - doubledFourierSingularFactor edges companion p‖ ≤
      (12 : ℝ) ^ Fintype.card (ι ⊕ ι) *
        (fourierPairComparisonConstant (Fintype.card (ι ⊕ ι)) / (p : ℝ) ^ 2 +
          doubledFourierExceptionalCost edges companion p * (2 * σ * Real.log p) / p) := by
    simpa only [univ_disjSum_univ_eq, Finset.card_univ, doubledFourierPrimeFactor,
      doubledFourierReferenceFactor, doubledFourierSingularFactor,
      fourierPairComparisonConstant, doubledFourierExceptionalCost] using! hbase
  unfold doubledFourierRelativeFactor
  rw [← div_div]
  calc
    _ ≤ 2 * ‖doubledFourierPrimeFactor edges companion s p /
        doubledFourierReferenceFactor s p - doubledFourierSingularFactor edges companion p‖ :=
      norm_div_sub_one_le_twice_sub
        (half_le_norm_doubledFourierSingularFactor edges companion hp hfour hedgeCard)
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)

end

end Erdos4b
