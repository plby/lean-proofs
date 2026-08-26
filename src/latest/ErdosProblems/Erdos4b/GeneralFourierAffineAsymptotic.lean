/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierScaleBounds
import ErdosProblems.Erdos4b.GeneralFourierActualSingularProduct

/-!
# Compact-profile asymptotics for the actual affine sieve

The abstract Fourier hypotheses are verified for the indexed primorial
tuple and its literal collision graph. The normalization uses the actual
forbidden-residue singular product, including the auxiliary prime.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

theorem affineDoubledFourierBoxConditions
    {K w m q : ℕ} {V : ℝ} (L : (Fin K ⊕ Fin K) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hw : 14 * K + 1 ≤ w) (hV : 1 ≤ V)
    (hL : ∀ i, 2 * (V + 1) ^ (3 / 4 : ℝ) ≤ L i) :
    DoubledFourierBoxConditions (m * crossExceptionalModulus (preSievedShifts K w) m q)
      w (indexedPreSievedFourierEdges K w m q) (affineFourierCompanionSwitch m)
      L (Real.sqrt V) (fourierQuarterExponent V) := by
  refine ⟨fun i ↦ fourierScale_pos_of_threeQuarter_bound hV (hL i),
    Nat.mul_pos hm (crossExceptionalModulus_pos (H := preSievedShifts K w) hm hq),
    by omega, fourierQuarterExponent_nonneg (by linarith), ?_, ?_, ?_,
    fun i ↦ sqrt_box_scale_le_fourierQuarterExponent hV (hL i)⟩
  · simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    have hwR : 14 * (K : ℝ) + 1 ≤ w := by exact_mod_cast hw
    linarith
  · intro p hwp
    simpa only [Fintype.card_fin] using
      card_indexedPreSievedFourierEdges_le p.property (by omega : K ≤ w) hwp
  · intro p hwp hnot
    exact indexedPreSievedFourierEdges_generic hnot

theorem exists_smoothCompactAffineProfileTensor_fourier_asymptotic
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
    ∃ cutoff : α → ℕ,
      Tendsto (fun a ↦ doubledFourierNormalization (w a)
        (indexedPreSievedFourierEdges K (w a) (m a) (q a))
        (affineFourierCompanionSwitch (m a)) (L a) *
        cutoffSelbergProfileTensorSum
          (selectedFourierPrimeCutoff (fun p ↦ decide (w a < p))
            (boundedFourierPrimes (cutoff a)))
          (indexedPreSievedFourierEdges K (w a) (m a) (q a))
          (affineFourierCompanionSwitch (m a)) F (fun i _ ↦ L a i)) l
        (𝓝 (∏ i, ∫ t : ℝ in Set.Ioi 0, deriv (F (i, false)) t * deriv (F (i, true)) t)) := by
  let M (a : α) := m a * crossExceptionalModulus (preSievedShifts K (w a)) (m a) (q a)
  apply exists_smoothCompactProfileTensor_normalized_asymptotic M w
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

def actualAffineFourierNormalization (K w m q : ℕ) (L : (Fin K ⊕ Fin K) → ℝ) : ℂ :=
  (∏ i, (L i : ℂ)) * smallDoubledFourierReferenceProduct (ι := Fin K) w (fun _ _ ↦ 0) /
    ∏' p : Nat.Primes, roughActualAffineSingularFactor (preSievedShifts K w) w m q p

theorem actualAffineFourierNormalization_eq_div_correction
    {K w m q : ℕ} (L : (Fin K ⊕ Fin K) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hw : 14 * K + 1 ≤ w) (hwq : w < q) :
    actualAffineFourierNormalization K w m q L =
      doubledFourierNormalization w (indexedPreSievedFourierEdges K w m q)
        (affineFourierCompanionSwitch m) L /
        affineAuxiliaryPrimeCorrection (preSievedShifts K w) m q := by
  have hlarge : 7 * (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℝ) ≤ w := by
    simp only [Fintype.card_sum, Fintype.card_coe, card_preSievedShifts, Nat.cast_add]
    have hwR : 14 * (K : ℝ) + 1 ≤ w := by exact_mod_cast hw
    linarith
  unfold actualAffineFourierNormalization doubledFourierNormalization
  rw [tprod_roughActualAffineSingularFactor_eq_indexed hm hq (by omega : K ≤ w) hwq hlarge,
    div_div]
  congr 1
  exact mul_comm _ _

theorem exists_smoothCompactAffineProfileTensor_actual_asymptotic
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
    ∃ cutoff : α → ℕ,
      Tendsto (fun a ↦ actualAffineFourierNormalization K (w a) (m a) (q a) (L a) *
        cutoffSelbergProfileTensorSum
          (selectedFourierPrimeCutoff (fun p ↦ decide (w a < p))
            (boundedFourierPrimes (cutoff a)))
          (indexedPreSievedFourierEdges K (w a) (m a) (q a))
          (affineFourierCompanionSwitch (m a)) F (fun i _ ↦ L a i)) l
        (𝓝 (∏ i, ∫ t : ℝ in Set.Ioi 0, deriv (F (i, false)) t * deriv (F (i, true)) t)) := by
  obtain ⟨cutoff, hc⟩ := exists_smoothCompactAffineProfileTensor_fourier_asymptotic
    K w m q V L hw hV hm hq hcutoff hmV hqV hLlower hLupper F hcompact hsmooth
  have hqTop : Tendsto q l atTop := tendsto_atTop_mono' l (hwq.mono fun a ha ↦ ha.le) hw
  have hcorr := tendsto_affineAuxiliaryPrimeCorrection_one K
    (fun a ↦ preSievedShifts K (w a)) m q (fun a ↦ card_preSievedShifts K (w a)) hq hqTop
  refine ⟨cutoff, ?_⟩
  have hlim := hc.div hcorr (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [div_one] at hlim
  apply hlim.congr'
  filter_upwards [hm, hq, hwq, hw.eventually_ge_atTop (14 * K + 1)] with a hma hqa hwqa hwa
  rw [actualAffineFourierNormalization_eq_div_correction (L a) hma hqa hwa hwqa,
    div_mul_eq_mul_div]
  rfl

end

end Erdos4b
