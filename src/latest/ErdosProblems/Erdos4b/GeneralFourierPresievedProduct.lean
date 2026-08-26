/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCutoffIntegral

/-!
# Euler cutoff removal with prescribed excluded primes

The pre-sieve removes its primes from the divisor Euler product. A fixed
Boolean selection covers this case without changing the factors at any
remaining prime. The same absolute majorant and integral limit apply.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def selectedDoubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  if select p then doubledFourierPrimeFactor edges companion s p else 1

theorem prod_selectedDoubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (Q : Finset Nat.Primes) :
    (∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion s p) =
      ∏ p ∈ Q.filter (fun p : Nat.Primes ↦ select p.val),
        doubledFourierPrimeFactor edges companion s p := by
  classical
  rw [Finset.prod_filter]
  rfl

theorem continuous_selectedDoubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) :
    Continuous (fun s : (ι ⊕ ι) → Bool → ℂ ↦
      selectedDoubledFourierPrimeFactor select edges companion s p) := by
  unfold selectedDoubledFourierPrimeFactor
  split_ifs
  · exact continuous_doubledFourierPrimeFactor edges companion p
  · exact continuous_const

theorem multipliable_selectedDoubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) :
    Multipliable (fun p : Nat.Primes ↦
      selectedDoubledFourierPrimeFactor select edges companion s p) := by
  have hsum := summable_norm_doubledFourierPrimeFactor_sub_one edges companion s hσ hs
  have hsmall : Summable (fun p : Nat.Primes ↦
      ‖selectedDoubledFourierPrimeFactor select edges companion s p - 1‖) := by
    apply Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) _ hsum
    intro p
    unfold selectedDoubledFourierPrimeFactor
    split_ifs <;> simp
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsmall

theorem norm_prod_selectedDoubledFourierPrimeFactor_le_zeta {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) (Q : Finset Nat.Primes) :
    ‖∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion s p‖ ≤
      ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  rw [prod_selectedDoubledFourierPrimeFactor]
  exact norm_prod_doubledFourierPrimeFactor_le_zeta edges companion s hσ hs _

theorem tendsto_integral_selectedDoubledFourierPrimeProducts
    {ι X : Type*} [Fintype ι] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (select : ℕ → Bool)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : X → (ι ⊕ ι) → Bool → ℂ) (hS : Continuous S)
    (G : X → ℂ) (hG : Integrable G μ) {σ : ℝ} (hσ : 1 < σ)
    (hRe : ∀ x i b, σ - 1 ≤ (S x i b).re) :
    Tendsto (fun Q : Finset Nat.Primes ↦ ∫ x,
      (∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion (S x) p) * G x ∂μ)
      atTop (𝓝 (∫ x,
        (∏' p : Nat.Primes,
          selectedDoubledFourierPrimeFactor select edges companion (S x) p) * G x ∂μ)) := by
  classical
  let C := ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι)
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * ‖G x‖)
  · apply Eventually.of_forall
    intro Q
    have hprod : Continuous (fun x ↦
        ∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion (S x) p) :=
      continuous_finsetProd Q fun p hp ↦
        (continuous_selectedDoubledFourierPrimeFactor select edges companion p).comp hS
    exact hprod.aestronglyMeasurable.mul hG.aestronglyMeasurable
  · apply Eventually.of_forall
    intro Q
    apply ae_of_all
    intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_prod_selectedDoubledFourierPrimeFactor_le_zeta
        select edges companion (S x) hσ (hRe x) Q)
      (norm_nonneg _)
  · exact hG.norm.const_mul C
  · apply ae_of_all
    intro x
    have hprod : Tendsto (fun Q : Finset Nat.Primes ↦
        ∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion (S x) p) atTop
        (𝓝 (∏' p : Nat.Primes,
          selectedDoubledFourierPrimeFactor select edges companion (S x) p)) :=
      (multipliable_selectedDoubledFourierPrimeFactor
        select edges companion (S x) hσ (hRe x)).hasProd
    exact hprod.mul_const (G x)

end

end Erdos4b
