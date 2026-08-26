/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierReferenceProduct
import ErdosProblems.Erdos4b.GeneralFourierSingularProduct
import ErdosProblems.Erdos4b.GeneralFourierRelativeLimit

/-!
# Exact factorization and relative error for the full doubled Euler kernel

The kernel is factored into the convergent relative product, the explicit
reference zeta quotient, and the nonzero singular product. Thus division
by the normalization is justified, not assumed.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem selectedDoubledFourierPrimeFactor_eq_three_factors
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {w : ℕ}
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (p : Nat.Primes) :
    selectedDoubledFourierPrimeFactor (fun p ↦ decide (w < p)) edges companion s p =
      roughDoubledFourierRelativeFactor w edges companion s p *
        (roughDoubledFourierReferenceFactor w s p *
          roughDoubledFourierSingularFactor w edges companion p) := by
  by_cases hwp : w < p.val
  · simp only [selectedDoubledFourierPrimeFactor, roughDoubledFourierRelativeFactor,
      roughDoubledFourierReferenceFactor, roughDoubledFourierSingularFactor,
      decide_eq_true_eq, if_pos hwp]
    have hpw : (w : ℝ) ≤ p := by exact_mod_cast hwp.le
    have hn : (0 : ℝ) ≤ Fintype.card (ι ⊕ ι) := Nat.cast_nonneg _
    exact doubledFourierPrimeFactor_eq_relative_mul edges companion s
      (by exact_mod_cast p.property.two_le) (by linarith) (hedgeCard p hwp) hRe
  · simp [selectedDoubledFourierPrimeFactor, roughDoubledFourierRelativeFactor,
      roughDoubledFourierReferenceFactor, roughDoubledFourierSingularFactor, hwp]

theorem hasProd_selectedDoubledFourierPrimeFactor_factorized
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {M w : ℕ} (hM : 0 < M) (hw : 0 < w)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 < (s i b).re) :
    HasProd (fun p : Nat.Primes ↦
      selectedDoubledFourierPrimeFactor (fun p ↦ decide (w < p)) edges companion s p)
      ((∏' p : Nat.Primes, roughDoubledFourierRelativeFactor w edges companion s p) *
        ((doubledFourierReferenceZetaProduct s / smallDoubledFourierReferenceProduct w s) *
          ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p)) := by
  let σ : ℝ := ∑ i, ‖s i false‖
  have hσ : 0 ≤ σ := Finset.sum_nonneg fun i hi ↦ norm_nonneg _
  have hNorm : ∀ i, ‖s i false‖ ≤ σ := by
    intro i
    exact Finset.single_le_sum (f := fun j ↦ ‖s j false‖)
      (fun j hj ↦ norm_nonneg _) (Finset.mem_univ i)
  have hR := multipliable_roughDoubledFourierRelativeFactor edges companion s
    hM hw hσ hcard hedgeCard hgeneric (fun i b ↦ (hRe i b).le) hNorm
  have hS := multipliable_roughDoubledFourierSingularFactor
    edges companion hM hcard hedgeCard hgeneric
  have h := hR.hasProd.mul ((hasProd_roughDoubledFourierReferenceFactor w s hRe).mul hS.hasProd)
  convert! h using 1
  ext p
  exact selectedDoubledFourierPrimeFactor_eq_three_factors edges companion s hcard hedgeCard
    (fun i b ↦ (hRe i b).le) p

theorem normalized_tprod_selectedDoubledFourierPrimeFactor_eq_relative
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {M w : ℕ} (hM : 0 < M) (hw : 0 < w)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 < (s i b).re) :
    (∏' p : Nat.Primes,
      selectedDoubledFourierPrimeFactor (fun p ↦ decide (w < p)) edges companion s p) /
      ((doubledFourierReferenceZetaProduct s / smallDoubledFourierReferenceProduct w s) *
        ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p) =
      ∏' p : Nat.Primes, roughDoubledFourierRelativeFactor w edges companion s p := by
  have hB0 := div_ne_zero (doubledFourierReferenceZetaProduct_ne_zero s hRe)
    (smallDoubledFourierReferenceProduct_ne_zero w s (fun i b ↦ (hRe i b).le))
  have hS0 := tprod_roughDoubledFourierSingularFactor_ne_zero
    edges companion hM hcard hedgeCard hgeneric
  apply (div_eq_iff (mul_ne_zero hB0 hS0)).mpr
  exact (hasProd_selectedDoubledFourierPrimeFactor_factorized
    edges companion s hM hw hcard hedgeCard hgeneric hRe).tprod_eq

theorem norm_normalized_tprod_selectedDoubledFourierPrimeFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {M w : ℕ} {σ : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 < (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    ‖(∏' p : Nat.Primes,
      selectedDoubledFourierPrimeFactor (fun p ↦ decide (w < p)) edges companion s p) /
      ((doubledFourierReferenceZetaProduct s / smallDoubledFourierReferenceProduct w s) *
        ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p) - 1‖ ≤
      Real.exp (doubledFourierRelativeErrorBound ι M w σ) - 1 := by
  rw [normalized_tprod_selectedDoubledFourierPrimeFactor_eq_relative
    edges companion s hM hw hcard hedgeCard hgeneric hRe]
  exact norm_tprod_roughDoubledFourierRelativeFactor_sub_one_le edges companion s
    hM hw hσ hcard hedgeCard hgeneric (fun i b ↦ (hRe i b).le) hNorm

end

end Erdos4b
