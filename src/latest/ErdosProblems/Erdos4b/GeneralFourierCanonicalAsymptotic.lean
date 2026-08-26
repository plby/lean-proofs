/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCanonicalCutoff
import ErdosProblems.Erdos4b.GeneralFourierAffineAsymptotic

/-!
# The normalized asymptotic at the canonical profile cutoff

The cutoff is fixed by the profiles and scales alone. This form of the
limit can be summed over finitely many profile pairs while keeping one
common coefficient support independent of the auxiliary prime.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

theorem compactSelbergProfileSum_normalized_integral
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) :
    doubledFourierNormalization w edges companion L *
        compactSelbergProfileSum (fun p ↦ decide (w < p)) edges companion
          (fun ib ↦ laplaceFourierProfile (f ib)) (fun i _ ↦ L i) =
      ∫ ξ, normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ := by
  rw [compactSelbergProfileSum_eq_fullEuler_integral _ edges companion hedges f hcompact
    (fun i _ ↦ L i) (fun i _ ↦ hL i), ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ ↦ (mul_assoc _ _ _).symm

theorem tendsto_compactSelbergProfileSum_normalized
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
      compactSelbergProfileSum (fun p ↦ decide (w a < p))
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
  have hlim := tendsto_integral_normalizedDoubledFourierKernel_log_envelope
    M w edges companion L σ V hdata hw hV hσ hlog hcutoff hB hsize hupper f
  rw [integral_doubledFourierPairKernel_mul_tensor_eq_given_profiles f F hf] at hlim
  apply hlim.congr'
  filter_upwards [hdata, hcoherent] with a ha hca
  have heq := compactSelbergProfileSum_normalized_integral
    (w a) (edges a) (companion a) hca f hcompact' (L a) ha.scale_pos
  simpa only [heqF] using heq.symm

theorem tendsto_compactAffineProfileSum_fourier_normalized
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (K : ℕ) (w m q : α → ℕ) (V : α → ℝ) (L : α → (Fin K ⊕ Fin K) → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hq : ∀ᶠ a in l, (q a).Prime)
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hqV : ∀ᶠ a in l, Real.log (q a) ≤ V a)
    (hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i)
    (hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (F : ((Fin K ⊕ Fin K) × Bool) → ℝ → ℂ)
    (hcompact : ∀ ib, HasCompactSupport (F ib)) (hsmooth : ∀ ib, ContDiff ℝ ∞ (F ib)) :
    Tendsto (fun a ↦ doubledFourierNormalization (w a)
      (indexedPreSievedFourierEdges K (w a) (m a) (q a))
      (affineFourierCompanionSwitch (m a)) (L a) *
      compactSelbergProfileSum (fun p ↦ decide (w a < p))
        (indexedPreSievedFourierEdges K (w a) (m a) (q a))
        (affineFourierCompanionSwitch (m a)) F (fun i _ ↦ L a i)) l
      (𝓝 (∏ i, ∫ t : ℝ in Set.Ioi 0, deriv (F (i, false)) t * deriv (F (i, true)) t)) := by
  let M (a : α) := m a * crossExceptionalModulus (preSievedShifts K (w a)) (m a) (q a)
  apply tendsto_compactSelbergProfileSum_normalized M w
    (fun a ↦ indexedPreSievedFourierEdges K (w a) (m a) (q a))
    (fun a ↦ affineFourierCompanionSwitch (m a)) L
    (fun a ↦ fourierQuarterExponent (V a)) V
  · filter_upwards [hm, hq, hw.eventually_ge_atTop (14 * K + 1),
      hV.eventually_ge_atTop 1, hLlower] with a hma hqa hwa hVa hLa
    exact affineDoubledFourierBoxConditions (L a) hma hqa hwa hVa hLa
  · exact Eventually.of_forall fun a p ij hij ↦
      indexedPreSievedFourierEdges_companion p.property ij hij
  · exact hw
  · exact hV
  · exact tendsto_fourierQuarterExponent_zero hV
  · exact tendsto_fourierQuarterExponent_mul_log_zero hV
  · exact hcutoff
  · exact (by positivity : 0 ≤ 1 + 4 * (K : ℝ) ^ 2)
  · filter_upwards [hm, hq, hmV, hqV,
      eventually_log_primorial_le_ambient w V hw hV hcutoff,
      hV.eventually_ge_atTop (Real.log ((K : ℝ) ^ 2 + 1))]
      with a hma hqa hmVa hqVa hPa hKa
    exact log_fullAffineExceptionalInteger_le K (w a) hma hqa hmVa hqVa hPa hKa
  · exact hLupper
  · exact hcompact
  · exact hsmooth

theorem tendsto_compactAffineProfileSum_actual_normalized
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (K : ℕ) (w m q : α → ℕ) (V : α → ℝ) (L : α → (Fin K ⊕ Fin K) → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hq : ∀ᶠ a in l, (q a).Prime)
    (hwq : ∀ᶠ a in l, w a < q a)
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hqV : ∀ᶠ a in l, Real.log (q a) ≤ V a)
    (hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i)
    (hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (F : ((Fin K ⊕ Fin K) × Bool) → ℝ → ℂ)
    (hcompact : ∀ ib, HasCompactSupport (F ib)) (hsmooth : ∀ ib, ContDiff ℝ ∞ (F ib)) :
    Tendsto (fun a ↦ actualAffineFourierNormalization K (w a) (m a) (q a) (L a) *
      compactSelbergProfileSum (fun p ↦ decide (w a < p))
        (indexedPreSievedFourierEdges K (w a) (m a) (q a))
        (affineFourierCompanionSwitch (m a)) F (fun i _ ↦ L a i)) l
      (𝓝 (∏ i, ∫ t : ℝ in Set.Ioi 0, deriv (F (i, false)) t * deriv (F (i, true)) t)) := by
  have hc := tendsto_compactAffineProfileSum_fourier_normalized
    K w m q V L hw hV hm hq hcutoff hmV hqV hLlower hLupper F hcompact hsmooth
  have hqTop : Tendsto q l atTop := tendsto_atTop_mono' l (hwq.mono fun a ha ↦ ha.le) hw
  have hcorr := tendsto_affineAuxiliaryPrimeCorrection_one K
    (fun a ↦ preSievedShifts K (w a)) m q (fun a ↦ card_preSievedShifts K (w a)) hq hqTop
  have hlim := hc.div hcorr (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [div_one] at hlim
  apply hlim.congr'
  filter_upwards [hm, hq, hwq, hw.eventually_ge_atTop (14 * K + 1)] with a hma hqa hwqa hwa
  rw [actualAffineFourierNormalization_eq_div_correction (L a) hma hqa hwa hwqa,
    div_mul_eq_mul_div]
  rfl

end

end Erdos4b
