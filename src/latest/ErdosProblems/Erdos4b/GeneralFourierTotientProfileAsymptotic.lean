/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCommonCutoff
import ErdosProblems.Erdos4b.GeneralFourierTotientFullIntegral
import ErdosProblems.Erdos4b.GeneralFourierTotientIntegralLimit
import ErdosProblems.Erdos4b.GeneralFourierMainIntegral

/-!
# Totient profile asymptotics at a graph-independent cutoff

Fixed compact smooth profiles determine their Fourier transforms once.
The common coordinate-capturing cutoff is independent of the varying
arithmetic parameters, and the limiting constant is the derivative-pair
integral, with no unproved analytic input.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

theorem compactTotientSelbergProfileSum_eq_fullEuler_integral
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w) :
    compactTotientSelbergProfileSum (fun p ↦ decide (w < p)) edges companion
      (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏' p : Nat.Primes, roughTotientDoubledFourierPrimeFactor w edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ := by
  classical
  let select (p : ℕ) := decide (w < p)
  let F := fun ib ↦ laplaceFourierProfile (f ib)
  let B := compactProfileTensorCommonBound F L
  obtain ⟨σ, hσ, hσL⟩ := exists_doubledFourierTensor_halfPlane L hL
  have hlimit := tendsto_integral_roughTotientDoubledFourierPrimeProducts volume w edges companion
    (doubledFourierTensorExponents L) (continuous_doubledFourierTensorExponents L)
    (doubledFourierTensor f) (integrable_doubledFourierTensor f) hσ hw0 hw
    (fun ξ i b ↦ by rw [doubledFourierTensorExponents_re]; exact hσL i b)
  have heventual : ∀ᶠ Q : Finset Nat.Primes in atTop,
      (∫ ξ, (∏ p ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ) =
      compactTotientSelbergProfileSum select edges companion F L := by
    filter_upwards [eventually_ge_atTop (boundedFourierPrimes B)] with Q hQ
    have hP := selectedFourierPrimeCutoff_prime select Q
    have hE : ∀ p ∈ selectedFourierPrimeCutoff select Q, ∀ ij ∈ edges p, companion p = true :=
      fun p hp ↦ hedges ⟨p, hP p hp⟩
    have hfinite := cutoffTotientSelbergProfileTensorSum_eq_integral_finiteEulerProduct
      (selectedFourierPrimeCutoff select Q) hP edges companion hE f L hL
    simp only [select] at hfinite
    simp_rw [prod_selectedFourierPrimeCutoff_totient w edges companion] at hfinite
    rw [← hfinite, ← (compactProfileTensorCommonBound_spec F hcompact L hL
      (selectedFourierPrimeCutoff select Q) hP edges companion).2,
      selectedFourierPrimeCutoff_filter_eq select B hQ]
    rfl
  have hconstant := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heventual)
  exact (tendsto_nhds_unique hlimit hconstant).symm

theorem compactTotientSelbergProfileSum_normalized_integral
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w) :
    doubledFourierNormalization w edges companion L *
        compactTotientSelbergProfileSum (fun p ↦ decide (w < p)) edges companion
          (fun ib ↦ laplaceFourierProfile (f ib)) (fun i _ ↦ L i) =
      ∫ ξ, normalizedTotientDoubledFourierKernel w edges companion L ξ *
        doubledFourierTensor f ξ := by
  rw [compactTotientSelbergProfileSum_eq_fullEuler_integral w edges companion hedges f hcompact
    (fun i _ ↦ L i) (fun i _ ↦ hL i) hw0 hw, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ ↦ (mul_assoc _ _ _).symm

theorem tendsto_compactTotientSelbergProfileSum_normalized
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
    Tendsto (fun a ↦ doubledFourierNormalization (w a) (edges a) (companion a) (L a) *
      compactTotientSelbergProfileSum (fun p ↦ decide (w a < p))
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
  have hlim := tendsto_integral_normalizedTotientDoubledFourierKernel_log_envelope
    M w edges companion L σ V hdata hw hV hσ hlog hcutoff hB hsize hupper f
  rw [integral_doubledFourierPairKernel_mul_tensor_eq_given_profiles f F hf] at hlim
  apply hlim.congr'
  filter_upwards [hdata, hcoherent, hw.eventually_gt_atTop 0,
    hw.eventually_ge_atTop (2 * Fintype.card (NonemptyDoubledPrimeChoice ι))]
    with a ha hca hw0 hwa
  have heq := compactTotientSelbergProfileSum_normalized_integral
    (w a) (edges a) (companion a) hca f hcompact' (L a) ha.scale_pos hw0
      (by exact_mod_cast hwa)
  simpa only [heqF] using heq.symm

end

end Erdos4b
