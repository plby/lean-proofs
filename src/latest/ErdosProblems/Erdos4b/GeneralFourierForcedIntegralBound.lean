/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedFullIntegral
import ErdosProblems.Erdos4b.GeneralFourierTotientScaledKernel

/-!
# The normalized forced profile sum is controlled by an absolute integral

The extra reciprocal-prime factor multiplies the integral of the norm
of the unforced normalized kernel. The norm of its integral is not used
as a substitute for this absolute-integrability estimate.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem norm_normalized_cutoffForcedSelbergProfileTensorSum_le
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ r : Nat.Primes, ∀ ij ∈ edges r, companion r = true)
    (p : Nat.Primes) (hwp : w < p.val)
    (R : ((ι ⊕ ι) → Bool → ℕ) → Prop) (force : DoubledPrimeChoice ι → Prop)
    (hR : ∀ (P : Finset ℕ), (∀ r ∈ P, r.Prime) → ∀ hpP : p.val ∈ P,
      ∀ c : P → DoubledPrimeChoice ι,
        R (doubledPrimeChoiceDivisor P c) ↔ force (c ⟨p.val, hpP⟩))
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ w)
    {B : ℕ} (hB : compactProfileTensorCommonBound
      (fun ib ↦ laplaceFourierProfile (f ib)) (fun i _ ↦ L i) ≤ B)
    (hint : Integrable (fun ξ ↦ normalizedTotientDoubledFourierKernel w edges companion L ξ *
      doubledFourierTensor f ξ)) :
    ‖doubledFourierNormalization w edges companion L *
      cutoffForcedSelbergProfileTensorSum
        (selectedFourierPrimeCutoff (fun r ↦ decide (w < r)) (boundedFourierPrimes B))
        edges companion p R (fun ib ↦ laplaceFourierProfile (f ib)) (fun i _ ↦ L i)‖ ≤
      (4 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ)) *
        ∫ ξ, ‖normalizedTotientDoubledFourierKernel w edges companion L ξ *
          doubledFourierTensor f ξ‖ := by
  let allow (c : DoubledPrimeChoice ι) :=
    DoubledPrimeChoiceAllowed (edges p) (companion p) c ∧ force c
  let H (ξ : ((ι ⊕ ι) × Bool) → ℝ) :=
    forcedTotientFourierPrimeFactor allow (doubledFourierTensorExponents (fun i _ ↦ L i) ξ) p /
      totientDoubledFourierPrimeFactor edges companion
        (doubledFourierTensorExponents (fun i _ ↦ L i) ξ) p
  have hp : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ (p : ℝ) :=
    hw.trans (by exact_mod_cast hwp.le)
  have hnorm (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
      ‖H ξ‖ ≤ 4 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ) := by
    apply norm_forcedTotientFourierPrimeFactor_div_le allow edges companion _ _ p hp
    intro i b
    rw [doubledFourierTensorExponents_re]
    exact (inv_pos.mpr (hL i)).le
  rw [cutoffForcedSelbergProfileTensorSum_eq_fullEuler_integral w edges companion hedges
    p hwp R force hR f hcompact (fun i _ ↦ L i) (fun i _ ↦ hL i) hw0 hw hB,
    ← integral_const_mul]
  calc
    _ = ‖∫ ξ, H ξ * (normalizedTotientDoubledFourierKernel w edges companion L ξ *
        doubledFourierTensor f ξ)‖ := by
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro ξ
      dsimp only [H, allow, normalizedTotientDoubledFourierKernel]
      ring
    _ ≤ ∫ ξ, (4 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ)) *
        ‖normalizedTotientDoubledFourierKernel w edges companion L ξ *
          doubledFourierTensor f ξ‖ := by
      apply norm_integral_le_of_norm_le
        (hint.norm.const_mul (4 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ)))
      apply ae_of_all
      intro ξ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hnorm ξ) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

end

end Erdos4b
