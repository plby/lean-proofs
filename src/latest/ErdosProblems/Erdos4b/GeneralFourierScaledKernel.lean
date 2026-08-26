/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFactorization
import ErdosProblems.Erdos4b.GeneralFourierSmallReference

/-!
# Exact scaled form of the Fourier kernel

The reference zeta quotients separate into the Fourier pair kernels,
the reciprocal logarithmic scales, and residue corrections. Combining
this with the arithmetic Euler factorization gives a literal identity
for the normalized kernel at every frequency.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def doubledFourierPairKernel {ι : Type*} [Fintype ι]
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) : ℂ :=
  ∏ i, fourierLaplacePairKernel (ξ (i, false)) (ξ (i, true))

def doubledFourierZetaCorrection {ι : Type*} [Fintype ι]
    (L : (ι ⊕ ι) → ℝ) (ξ : ((ι ⊕ ι) × Bool) → ℝ) : ℂ :=
  ∏ i, selbergZetaQuotientCorrection
    (fourierLaplaceParameter (ξ (i, false)) / (L i : ℂ))
    (fourierLaplaceParameter (ξ (i, true)) / (L i : ℂ))

def doubledFourierNormalization {ι : Type*} [Fintype ι]
    (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → ℝ) : ℂ :=
  (∏ i, (L i : ℂ)) * smallDoubledFourierReferenceProduct (ι := ι) w (fun _ _ ↦ 0) /
    ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p

def normalizedDoubledFourierKernel {ι : Type*} [Fintype ι]
    (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → ℝ) (ξ : ((ι ⊕ ι) × Bool) → ℝ) : ℂ :=
  doubledFourierNormalization w edges companion L *
    ∏' p : Nat.Primes, selectedDoubledFourierPrimeFactor (fun p ↦ decide (w < p))
      edges companion (doubledFourierTensorExponents (fun i _ ↦ L i) ξ) p

theorem scaled_doubledFourierReferenceZetaProduct_eq
    {ι : Type*} [Fintype ι] (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, L i ≠ 0)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    (∏ i, (L i : ℂ)) *
      doubledFourierReferenceZetaProduct (doubledFourierTensorExponents (fun i _ ↦ L i) ξ) =
      doubledFourierPairKernel ξ * doubledFourierZetaCorrection L ξ := by
  unfold doubledFourierReferenceZetaProduct doubledFourierTensorExponents
    doubledFourierPairKernel doubledFourierZetaCorrection
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← add_assoc, selbergFourierZetaQuotient_identity _ _ (hL i)]
  have hLC : (L i : ℂ) ≠ 0 := by exact_mod_cast hL i
  field_simp

theorem fourierNormalization_factorization_identity {a b c d r z k : ℂ}
    (hc : c ≠ 0) (hd : d ≠ 0) (h : a * z = k) :
    (a * b / d) * (r * (z / c * d)) = k * (b / c * r) := by
  rw [← h]
  field_simp

theorem normalizedDoubledFourierKernel_eq_main_mul_corrections
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) {M w : ℕ} (hM : 0 < M) (hw : 0 < w)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    normalizedDoubledFourierKernel w edges companion L ξ =
      doubledFourierPairKernel ξ *
        ((smallDoubledFourierReferenceProduct (ι := ι) w (fun _ _ ↦ 0) /
          smallDoubledFourierReferenceProduct w
            (doubledFourierTensorExponents (fun i _ ↦ L i) ξ)) *
          (∏' p : Nat.Primes, roughDoubledFourierRelativeFactor w edges companion
            (doubledFourierTensorExponents (fun i _ ↦ L i) ξ) p) *
          doubledFourierZetaCorrection L ξ) := by
  let s := doubledFourierTensorExponents (fun i _ ↦ L i) ξ
  have hRe : ∀ i b, 0 < (s i b).re := by
    intro i b
    rw [doubledFourierTensorExponents_re]
    exact inv_pos.mpr (hL i)
  have hB0 := smallDoubledFourierReferenceProduct_ne_zero w s
    (fun i b ↦ (hRe i b).le)
  have hS0 := tprod_roughDoubledFourierSingularFactor_ne_zero
    edges companion hM hcard hedgeCard hgeneric
  unfold normalizedDoubledFourierKernel doubledFourierNormalization
  rw [(hasProd_selectedDoubledFourierPrimeFactor_factorized
    edges companion s hM hw hcard hedgeCard hgeneric hRe).tprod_eq]
  rw [fourierNormalization_factorization_identity hB0 hS0
    (scaled_doubledFourierReferenceZetaProduct_eq L (fun i ↦ (hL i).ne') ξ)]
  ring

theorem stronglyMeasurable_normalizedDoubledFourierKernel
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) :
    StronglyMeasurable (normalizedDoubledFourierKernel w edges companion L) := by
  apply StronglyMeasurable.const_mul
  apply StronglyMeasurable.tprod
  intro p
  exact ((continuous_selectedDoubledFourierPrimeFactor
    (fun p ↦ decide (w < p)) edges companion p).comp
      (continuous_doubledFourierTensorExponents (fun i _ ↦ L i))).stronglyMeasurable

end

end Erdos4b
