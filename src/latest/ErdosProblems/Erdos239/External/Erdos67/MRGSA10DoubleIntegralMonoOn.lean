import ErdosProblems.Erdos239.External.Erdos67.MRGSA10DoubleIntegralMajorantOn

/-! Rectangle-local monotonicity for two nested interval integrals. -/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

theorem doubleIntervalIntegral_mono_continuousOn
    {F G : ℝ → ℝ → ℝ} {eta : ℝ} (heta : 0 ≤ eta)
    (hF : ContinuousOn (Function.uncurry F)
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta))
    (hG : ContinuousOn (Function.uncurry G)
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta))
    (hle : ∀ alpha ∈ Icc (0 : ℝ) eta,
      ∀ beta ∈ Icc (0 : ℝ) eta, F alpha beta ≤ G alpha beta) :
    (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
      ∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta := by
  let c : ℝ → ℝ := fun x ↦ (Set.projIcc (0 : ℝ) eta heta x : ℝ)
  let C : ℝ × ℝ → ℝ × ℝ := fun z ↦ (c z.1, c z.2)
  let F' : ℝ → ℝ → ℝ := fun alpha beta ↦ F (c alpha) (c beta)
  let G' : ℝ → ℝ → ℝ := fun alpha beta ↦ G (c alpha) (c beta)
  have hc : Continuous c := by
    dsimp only [c]
    exact continuous_subtype_val.comp continuous_projIcc
  have hc_mem : ∀ x, c x ∈ Icc (0 : ℝ) eta := by
    intro x
    exact (Set.projIcc (0 : ℝ) eta heta x).property
  have hC : Continuous C := by
    dsimp only [C]
    exact (hc.comp continuous_fst).prodMk (hc.comp continuous_snd)
  have hC_mem : ∀ z, C z ∈ Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta := by
    intro z
    exact ⟨hc_mem z.1, hc_mem z.2⟩
  have hF' : Continuous (Function.uncurry F') := by
    change Continuous (Function.uncurry F ∘ C)
    exact hF.comp_continuous hC hC_mem
  have hG' : Continuous (Function.uncurry G') := by
    change Continuous (Function.uncurry G ∘ C)
    exact hG.comp_continuous hC hC_mem
  have hc_eq : ∀ x ∈ Icc (0 : ℝ) eta, c x = x := by
    intro x hx
    dsimp only [c]
    exact congrArg Subtype.val (Set.projIcc_of_mem heta hx)
  have hFint :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F' alpha beta) =
      ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F alpha beta := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    have halpha' : alpha ∈ Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using halpha
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using hbeta
    simp only [F', hc_eq alpha halpha', hc_eq beta hbeta']
  have hGint :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, G' alpha beta) =
      ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, G alpha beta := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    have halpha' : alpha ∈ Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using halpha
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Icc (0 : ℝ) eta := by
      simpa only [Set.uIcc_of_le heta] using hbeta
    simp only [G', hc_eq alpha halpha', hc_eq beta hbeta']
  have hmono :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F' alpha beta) ≤
      ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, G' alpha beta := by
    apply intervalIntegral.integral_mono_on heta
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hF' 0 eta).intervalIntegrable 0 eta
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hG' 0 eta).intervalIntegrable 0 eta
    · intro alpha halpha
      apply intervalIntegral.integral_mono_on heta
      · exact (hF'.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      · exact (hG'.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      · intro beta hbeta
        exact hle (c alpha) (hc_mem alpha) (c beta) (hc_mem beta)
  simpa only [hFint, hGint] using hmono

end


end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.doubleIntervalIntegral_mono_continuousOn
