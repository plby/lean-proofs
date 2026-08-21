import ErdosProblems.Erdos239.External.Erdos67.MRGSA10DoubleIntegralMajorant

/-!
# Rectangle-local double interval-integral majorants

The moving Perron line used in GS A.10 is regular on the source rectangle,
but it need not be regular after the two source parameters are continued to
all of `ℝ × ℝ`.  This file localizes the elementary double-integral
majorant accordingly.  The proof projects both parameters back to the closed
source interval and applies the global lemma to that continuous extension.
-/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The pointwise double-integral comparison only needs continuity on the
closed rectangle actually traversed by the two interval integrals. -/
theorem norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise_continuousOn
    {P Q : ℝ → ℝ → ℂ} {G : ℝ → ℝ → ℝ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hP : ContinuousOn (Function.uncurry P)
      (Set.Icc (0 : ℝ) eta ×ˢ Set.Icc (0 : ℝ) eta))
    (hQ : ContinuousOn (Function.uncurry Q)
      (Set.Icc (0 : ℝ) eta ×ˢ Set.Icc (0 : ℝ) eta))
    (hG : ContinuousOn (Function.uncurry G)
      (Set.Icc (0 : ℝ) eta ×ˢ Set.Icc (0 : ℝ) eta))
    (hmajor : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta) :
    ‖2 * (∫ alpha in 0..eta, ∫ beta in 0..eta, P alpha beta) -
        2 * (∫ alpha in 0..eta, ∫ beta in 0..eta, Q alpha beta)‖ ≤
      2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, G alpha beta := by
  let c : ℝ → ℝ := fun x ↦ (Set.projIcc (0 : ℝ) eta heta x : ℝ)
  let C : ℝ × ℝ → ℝ × ℝ := fun z ↦ (c z.1, c z.2)
  let P' : ℝ → ℝ → ℂ := fun alpha beta ↦ P (c alpha) (c beta)
  let Q' : ℝ → ℝ → ℂ := fun alpha beta ↦ Q (c alpha) (c beta)
  let G' : ℝ → ℝ → ℝ := fun alpha beta ↦ G (c alpha) (c beta)
  have hc : Continuous c := by
    dsimp only [c]
    exact continuous_subtype_val.comp continuous_projIcc
  have hc_mem : ∀ x, c x ∈ Set.Icc (0 : ℝ) eta := by
    intro x
    exact (Set.projIcc (0 : ℝ) eta heta x).property
  have hC : Continuous C := by
    dsimp only [C]
    exact (hc.comp continuous_fst).prodMk (hc.comp continuous_snd)
  have hC_mem : ∀ z, C z ∈
      Set.Icc (0 : ℝ) eta ×ˢ Set.Icc (0 : ℝ) eta := by
    intro z
    exact ⟨hc_mem z.1, hc_mem z.2⟩
  have hP' : Continuous (Function.uncurry P') := by
    change Continuous (Function.uncurry P ∘ C)
    exact hP.comp_continuous hC hC_mem
  have hQ' : Continuous (Function.uncurry Q') := by
    change Continuous (Function.uncurry Q ∘ C)
    exact hQ.comp_continuous hC hC_mem
  have hG' : Continuous (Function.uncurry G') := by
    change Continuous (Function.uncurry G ∘ C)
    exact hG.comp_continuous hC hC_mem
  have hc_eq : ∀ x ∈ Set.Icc (0 : ℝ) eta, c x = x := by
    intro x hx
    dsimp only [c]
    exact congrArg Subtype.val (Set.projIcc_of_mem heta hx)
  have hPint :
      (∫ alpha in (0 : ℝ)..eta, ∫ beta in (0 : ℝ)..eta,
        P' alpha beta) =
      ∫ alpha in (0 : ℝ)..eta, ∫ beta in (0 : ℝ)..eta,
        P alpha beta := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    have halpha' : alpha ∈ Set.Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using halpha
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Set.Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using hbeta
    simp only [P', hc_eq alpha halpha', hc_eq beta hbeta']
  have hQint :
      (∫ alpha in (0 : ℝ)..eta, ∫ beta in (0 : ℝ)..eta,
        Q' alpha beta) =
      ∫ alpha in (0 : ℝ)..eta, ∫ beta in (0 : ℝ)..eta,
        Q alpha beta := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    have halpha' : alpha ∈ Set.Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using halpha
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Set.Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using hbeta
    simp only [Q', hc_eq alpha halpha', hc_eq beta hbeta']
  have hGint :
      (∫ alpha in (0 : ℝ)..eta, ∫ beta in (0 : ℝ)..eta,
        G' alpha beta) =
      ∫ alpha in (0 : ℝ)..eta, ∫ beta in (0 : ℝ)..eta,
        G alpha beta := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    have halpha' : alpha ∈ Set.Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using halpha
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Set.Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using hbeta
    simp only [G', hc_eq alpha halpha', hc_eq beta hbeta']
  have hmajor' : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        ‖P' alpha beta - Q' alpha beta‖ ≤ G' alpha beta := by
    intro alpha halpha beta hbeta
    simpa only [P', Q', G', hc_eq alpha halpha, hc_eq beta hbeta] using
      hmajor alpha halpha beta hbeta
  have h := norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise
    (P := P') (Q := Q') (G := G') heta hP' hQ' hG' hmajor'
  simpa only [hPint, hQint, hGint] using h

end

end Erdos67.MRHalaszBands
