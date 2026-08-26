/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierLogEnvelope
import ErdosProblems.Erdos4b.GeneralFourierMainIntegral

/-!
# Normalized asymptotics for the finite compact-profile divisor sum

The Schwartz coefficients are chosen once from the fixed smooth profiles,
independently of all arithmetic parameters. Compact support supplies
finite prime cutoffs, and the exact integral identity transfers the
proved analytic limit back to the finite arithmetic coefficient sums.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

theorem exists_compactProfileTensor_normalized_integral
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ B : ℕ,
      doubledFourierNormalization w edges companion L *
        cutoffSelbergProfileTensorSum
          (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes B))
          edges companion (fun ib ↦ laplaceFourierProfile (f ib)) (fun i _ ↦ L i) =
      ∫ ξ, normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ := by
  obtain ⟨B, hB⟩ := exists_compactProfileTensor_fullEuler_integral
    (fun p ↦ decide (w < p)) edges companion hedges f hcompact
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
  refine ⟨B, ?_⟩
  rw [hB, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  exact (mul_assoc _ _ _).symm

theorem exists_smoothCompactProfileTensor_normalized_asymptotic
    {α ι : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (σ V : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (Real.sqrt (V a)) (σ a))
    (hcoherent : ∀ᶠ a in l, ∀ p : Nat.Primes, ∀ ij ∈ edges a p, companion a p = true)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hσ : Tendsto σ l (𝓝 0))
    (hlog : Tendsto (fun a ↦ σ a * Real.log (V a + 1)) l (𝓝 0))
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ᶠ a in l, Real.log (M a) ≤ B * V a)
    (hupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ)
    (hcompact : ∀ ib, HasCompactSupport (F ib)) (hsmooth : ∀ ib, ContDiff ℝ ∞ (F ib)) :
    ∃ cutoff : α → ℕ,
      Tendsto (fun a ↦ doubledFourierNormalization (w a) (edges a) (companion a) (L a) *
        cutoffSelbergProfileTensorSum
          (selectedFourierPrimeCutoff (fun p ↦ decide (w a < p))
            (boundedFourierPrimes (cutoff a)))
          (edges a) (companion a) F (fun i _ ↦ L a i)) l
        (𝓝 (∏ i, ∫ t : ℝ in Set.Ioi 0, deriv (F (i, false)) t * deriv (F (i, true)) t)) := by
  classical
  choose f hf using fun ib ↦ exists_schwartz_laplaceFourierProfile (F ib) (hcompact ib) (hsmooth ib)
  have heqF : (fun ib ↦ laplaceFourierProfile (f ib)) = F := by
    funext ib t
    exact hf ib t
  have hcompact' : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)) := by
    intro ib
    simpa only [show laplaceFourierProfile (f ib) = F ib from funext (hf ib)] using hcompact ib
  have hcutoffExists (a : α) : ∃ cutoff : ℕ,
      ((∀ i, 0 < L a i) ∧
        (∀ p : Nat.Primes, ∀ ij ∈ edges a p, companion a p = true)) →
      doubledFourierNormalization (w a) (edges a) (companion a) (L a) *
        cutoffSelbergProfileTensorSum
          (selectedFourierPrimeCutoff (fun p ↦ decide (w a < p)) (boundedFourierPrimes cutoff))
          (edges a) (companion a) F (fun i _ ↦ L a i) =
      ∫ ξ, normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ := by
    by_cases ha : (∀ i, 0 < L a i) ∧
      (∀ p : Nat.Primes, ∀ ij ∈ edges a p, companion a p = true)
    · obtain ⟨cutoff, hc⟩ := exists_compactProfileTensor_normalized_integral
        (w a) (edges a) (companion a) ha.2 f hcompact' (L a) ha.1
      exact ⟨cutoff, fun _ ↦ by simpa only [heqF] using hc⟩
    · exact ⟨0, fun h ↦ (ha h).elim⟩
  choose cutoff hcutoffEq using hcutoffExists
  refine ⟨cutoff, ?_⟩
  have hlim := tendsto_integral_normalizedDoubledFourierKernel_log_envelope
    M w edges companion L σ V hdata hw hV hσ hlog hcutoff hB hsize hupper f
  rw [integral_doubledFourierPairKernel_mul_tensor_eq_given_profiles f F hf] at hlim
  apply hlim.congr'
  filter_upwards [hdata, hcoherent] with a ha hca
  exact (hcutoffEq a ⟨ha.scale_pos, hca⟩).symm

end

end Erdos4b
