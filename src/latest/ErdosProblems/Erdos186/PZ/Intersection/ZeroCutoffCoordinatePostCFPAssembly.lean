/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.CoordinateCenterCanonicalPostCFPAssembly
import ErdosProblems.Erdos186.PZ.Intersection.ZeroCutoffCoordinateCenterError
import ErdosProblems.Erdos186.PZ.Intersection.BoundedSupportHighCoefficientPostCFPAssembly

/-!
# Zero-cutoff post-CFP assembly with coordinatewise center error
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace Theorem4PostCFPData

/-- Source-width-preserving bounded-support assembly at cutoff zero. -/
def ofHighCoefficientSideSelection_boundedSupport_zeroCutoff_coordinateCenter
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu gamma : ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma)
    (hr : 0 < (selector.chosen A hA).dimension)
    (hmu : 0 < mu) (hgamma : 0 < gamma)
    (hfull₁ :
      ((2 ^ (selector.chosen A hA).dimension *
        (2 * (selector.chosen A hA).dimension + 1) ^
          ((selector.chosen A hA).dimension - 1) *
        sourceControlCardMultiplier selector hA : ℕ) : ℝ) <
        (E.side₁.dilation : ℝ) * gamma)
    (hfull₂ :
      ((2 ^ (selector.chosen A hA).dimension *
        (2 * (selector.chosen A hA).dimension + 1) ^
          ((selector.chosen A hA).dimension - 1) *
        sourceControlCardMultiplier selector hA : ℕ) : ℝ) <
        (E.side₂.dilation : ℝ) * gamma)
    (hanisotropic₁ :
      ((selector.chosen A hA).dimension : ℝ) *
        (sourceAnisotropicConstant context
          (selector.chosen A hA).dimension : ℝ) ≤
        gamma * E.side₁.dilation)
    (hanisotropic₂ :
      ((selector.chosen A hA).dimension : ℝ) *
        (sourceAnisotropicConstant context
          (selector.chosen A hA).dimension : ℝ) ≤
        gamma * E.side₂.dilation)
    (hthick₁ : ∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) +
          E.forwardZeroCoordinateCenterError i) →
      y ∈ centeredZonotope E.forwardRoundingCore
        (D.scaledForwardCoefficient (highCoefficientZonotopeScale D)))
    (hthick₂ : ∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) +
          E.reverseZeroCoordinateCenterError i) →
      y ∈ centeredZonotope E.reverseRoundingCore
        (D.scaledReverseCoefficient (highCoefficientZonotopeScale D))) :
    { Dout : Theorem4PostCFPData (selector.chosen A hA).identifiedCore //
      Dout.a = D.a } := by
  let S := selector.chosen A hA
  let scale := highCoefficientZonotopeScale D
  let W₁ := E.forwardWitness
  let W₂ := E.reverseWitness
  let core₁ := E.forwardRoundingCore
  let core₂ := E.reverseRoundingCore
  let m := sourceControlScale selector hA
  let Q := sourceControlCardMultiplier selector hA
  let B := controlIntegerBox S.progression m
  let width : Fin S.dimension → ℝ :=
    fun i ↦ (S.progression.widths i - 1 : ℕ)
  have hscale : 0 ≤ scale := D.highCoefficientZonotopeScale_nonneg hmu
  have hhalf : scale * (mu * S.identifiedCore.card)⁻¹ = (1 : ℝ) / 2 :=
    D.highCoefficientZonotopeScale_mul_cap hmu
  have haBox : D.a ∈ (gapCoefficientBox S.progression).carrier :=
    S.identifiedCore_subset_coefficientBox D.a_mem
  have hH₁box : D.largeA₁ 0 ⊆
      (gapCoefficientBox S.progression).carrier :=
    (D.largeA₁_subset 0).trans
      ((D.A₁_subset_erase.trans (Finset.erase_subset _ _)).trans
        S.identifiedCore_subset_coefficientBox)
  have hH₂box : D.largeA₂ 0 ⊆
      (gapCoefficientBox S.progression).carrier :=
    (D.largeA₂_subset 0).trans
      ((D.A₂_subset_erase.trans (Finset.erase_subset _ _)).trans
        S.identifiedCore_subset_coefficientBox)
  have hA₁ : D.largeA₁ 0 ⊆ S.identifiedCore.erase D.a :=
    (D.largeA₁_subset 0).trans D.A₁_subset_erase
  have hA₂ : D.largeA₂ 0 ⊆ S.identifiedCore.erase D.a :=
    (D.largeA₂_subset 0).trans D.A₂_subset_erase
  have hdisjoint : Disjoint (D.largeA₁ 0) (D.largeA₂ 0) :=
    D.disjoint.mono (D.largeA₁_subset 0) (D.largeA₂_subset 0)
  have hrank₁ : W₁.rank = S.dimension := E.forwardWitness_rank
  have hrank₂ : W₂.rank = S.dimension := E.reverseWitness_rank
  have hwidth : ∀ i, 0 < width i := by
    intro i
    dsimp only [width]
    have hi : 0 < S.progression.widths i - 1 := by
      apply Nat.sub_pos_of_lt
      exact lt_of_lt_of_le (by decide : 1 < 3) (S.witness.three_le_width i)
    exact Nat.cast_pos.mpr hi
  have hcoreBound₁ : ∀ x ∈ core₁, ∀ i, |(x i : ℝ)| ≤ width i := by
    intro x hx i
    have hxInput := W₁.core_subset (canonicalRoundingCore_subset_core W₁ hx)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxInput
    have hdiff := Reduction.GAP.sub_mem_differenceCoefficientGAP_of_mem
      S.progression (hH₁box hy) haBox
    have hb := abs_coordinate_le_width_sub_one_of_mem_difference
      S.progression (y - D.a) hdiff i
    have hbReal : (|(y - D.a) i| : ℝ) ≤
        ((S.progression.widths i - 1 : ℕ) : ℝ) := by exact_mod_cast hb
    simpa only [orientedDeviation, Pi.sub_apply, Int.cast_abs, Int.cast_sub,
      width] using hbReal
  have hcoreBound₂ : ∀ x ∈ core₂, ∀ i, |(x i : ℝ)| ≤ width i := by
    intro x hx i
    have hxInput := W₂.core_subset (canonicalRoundingCore_subset_core W₂ hx)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxInput
    have hdiff := Reduction.GAP.sub_mem_differenceCoefficientGAP_of_mem
      S.progression (hH₂box hy) haBox
    have hb := abs_coordinate_le_width_sub_one_of_mem_difference
      S.progression (y - D.a) hdiff i
    have hbReal : (|(y - D.a) i| : ℝ) ≤
        ((S.progression.widths i - 1 : ℕ) : ℝ) := by exact_mod_cast hb
    simpa only [orientedDeviation, Pi.sub_apply, Int.cast_abs, Int.cast_sub,
      width, abs_sub_comm] using hbReal
  have hcontain₁ : W₁.progression.carrier ⊆
      CFP.translate E.translate₁ B.carrier := by
    rw [show W₁.progression.carrier = E.side₁.progression.carrier by
      exact E.forwardWitness_progression_carrier]
    simpa only [B, m] using E.contained₁
  have hcontain₂ : W₂.progression.carrier ⊆
      CFP.translate (-E.translate₂) B.carrier := by
    rw [show W₂.progression.carrier =
        E.side₂.progression.carrier.image (fun x ↦ -x) by
      exact E.reverseWitness_progression_carrier]
    simpa only [negatedGAP.carrier, B, m] using
      negatedGAP_carrier_subset_translate_controlIntegerBox
        S.progression m E.side₂.progression E.translate₂ E.contained₂
  have hvolume₁ : gamma * (S.progression.volume : ℝ) ≤
      (W₁.progression.volume : ℝ) := by
    rw [show W₁.progression.volume = E.side₁.progression.volume by
      exact E.forwardWitness_progression_volume]
    exact E.volume₁
  have hvolume₂ : gamma * (S.progression.volume : ℝ) ≤
      (W₂.progression.volume : ℝ) := by
    rw [show W₂.progression.volume = E.side₂.progression.volume by
      exact E.reverseWitness_progression_volume]
    exact E.volume₂
  have hbox : B.carrier.card ≤ Q * S.progression.volume := by
    simpa only [B, Q, m] using E.controlBox_card
  have hdet₁ : (stepMatrix (rankCastGAP W₁.progression hrank₁)).det ≠ 0 := by
    apply det_ne_zero_of_controlled_box_gamma_hierarchy_pos hr
      (rankCastGAP W₁.progression hrank₁) S.progression B E.translate₁ gamma
    · simpa only [rankCastGAP_carrier] using hcontain₁
    · exact rankCastGAP_nondegenerate hrank₁ W₁.progression_nondegenerate
    · exact rankCastGAP_dilate_proper hrank₁ W₁.dilate_proper
    · exact W₁.k_pos
    · exact hbox
    · simpa only [rankCastGAP_volume] using hvolume₁
    · exact hgamma
    · simpa only [S, Q] using hfull₁
  have hdet₂ : (stepMatrix (rankCastGAP W₂.progression hrank₂)).det ≠ 0 := by
    apply det_ne_zero_of_controlled_box_gamma_hierarchy_pos hr
      (rankCastGAP W₂.progression hrank₂) S.progression B (-E.translate₂) gamma
    · simpa only [rankCastGAP_carrier] using hcontain₂
    · exact rankCastGAP_nondegenerate hrank₂ W₂.progression_nondegenerate
    · exact rankCastGAP_dilate_proper hrank₂ W₂.dilate_proper
    · exact W₂.k_pos
    · exact hbox
    · simpa only [rankCastGAP_volume] using hvolume₂
    · exact hgamma
    · simpa only [S, Q] using hfull₂
  let radii₁ : Fin S.dimension → ℕ := Classical.choose
    (rankCastGAP_symmetric hrank₁ W₁.progression_symmetric)
  have hcentered₁ : (rankCastGAP W₁.progression hrank₁).Centered radii₁ :=
    Classical.choose_spec
      (rankCastGAP_symmetric hrank₁ W₁.progression_symmetric)
  let radii₂ : Fin S.dimension → ℕ := Classical.choose
    (rankCastGAP_symmetric hrank₂ W₂.progression_symmetric)
  have hcentered₂ : (rankCastGAP W₂.progression hrank₂).Centered radii₂ :=
    Classical.choose_spec
      (rankCastGAP_symmetric hrank₂ W₂.progression_symmetric)
  have hm : 0 < m := by
    dsimp only [m, sourceControlScale]
    exact Nat.mul_pos (by omega) (context.scaleDen_pos S.dimension)
  have herror₁ : ∀ e : LatticePoint S.dimension,
      e ∈ gapStepLattice W₁.progression →
      (∀ i, |(e i : ℝ)| ≤ (S.dimension : ℝ) * width i) →
      e ∈ (W₁.progression.dilate E.side₁.dilation).carrier := by
    apply enhancedWitness_anisotropic_errorBox_of_sourceControlBox_pos
      hr W₁ hrank₁ S.progression m hm E.translate₁ hcentered₁
      (by simpa only [rankCastGAP_carrier] using hcontain₁)
      gamma (S.dimension : ℝ) hgamma (by positivity)
      (by simpa only [rankCastGAP_volume] using hvolume₁) hdet₁
    simpa only [sourceAnisotropicConstant, sourceControlDilation,
      sourceControlScale, S, W₁, m, width] using hanisotropic₁
  have herror₂ : ∀ e : LatticePoint S.dimension,
      e ∈ gapStepLattice W₂.progression →
      (∀ i, |(e i : ℝ)| ≤ (S.dimension : ℝ) * width i) →
      e ∈ (W₂.progression.dilate E.side₂.dilation).carrier := by
    apply enhancedWitness_anisotropic_errorBox_of_sourceControlBox_pos
      hr W₂ hrank₂ S.progression m hm (-E.translate₂) hcentered₂
      (by simpa only [rankCastGAP_carrier] using hcontain₂)
      gamma (S.dimension : ℝ) hgamma (by positivity)
      (by simpa only [rankCastGAP_volume] using hvolume₂) hdet₂
    simpa only [sourceAnisotropicConstant, sourceControlDilation,
      sourceControlScale, S, W₂, m, width] using hanisotropic₂
  have hq₁ : ∀ x ∈ core₁,
      0 ≤ D.scaledForwardCoefficient scale x ∧
        D.scaledForwardCoefficient scale x ≤ (1 : ℝ) / 2 := by
    intro x hx
    have hb := D.scaledForwardCoefficient_bounds_on_canonicalRoundingCore
      hscale W₁ x hx
    exact ⟨hb.1, hb.2.trans hhalf.le⟩
  have hq₂ : ∀ x ∈ core₂,
      0 ≤ D.scaledReverseCoefficient scale x ∧
        D.scaledReverseCoefficient scale x ≤ (1 : ℝ) / 2 := by
    intro x hx
    have hb := D.scaledReverseCoefficient_bounds_on_canonicalRoundingCore
      hscale W₂ x hx
    exact ⟨hb.1, hb.2.trans hhalf.le⟩
  have hp₁ : W₁.translatePoint ∈ CFP.translate W₁.translatePoint
      (W₁.progression.dilate 0).carrier := by
    apply CFP.mem_translate_iff.mpr
    exact ⟨0, (W₁.progression_symmetric.dilate 0).zero_mem_carrier, by simp⟩
  have hp₂ : W₂.translatePoint ∈ CFP.translate W₂.translatePoint
      (W₂.progression.dilate 0).carrier := by
    apply CFP.mem_translate_iff.mpr
    exact ⟨0, (W₂.progression_symmetric.dilate 0).zero_mem_carrier, by simp⟩
  have hcenter₁ : ∀ i,
      |E.commonCenter i -
        (realVector W₁.translatePoint +
          zonotopeCenter core₁ (D.scaledForwardCoefficient scale)) i| ≤
        E.forwardZeroCoordinateCenterError i := by
    intro i
    simpa only [S, scale, W₁, core₁] using
      E.commonCenter_forward_zero_coordinate_error hmu i
  have hcenter₂ : ∀ i,
      |E.commonCenter i -
        (realVector W₂.translatePoint +
          zonotopeCenter core₂ (D.scaledReverseCoefficient scale)) i| ≤
        E.reverseZeroCoordinateCenterError i := by
    intro i
    simpa only [S, scale, W₂, core₂] using
      E.commonCenter_reverse_zero_coordinate_error hmu i
  exact
    ofCanonicalTargets_controlledBoxGammaHierarchy_anisotropic_finrank_pos_coordinateCenterError
      hr D.a_mem hA₁ hA₂ hdisjoint W₁ W₂ hrank₁ hrank₂
      core₁ core₂ (reserved_disjoint_canonicalRoundingCore W₁)
      (reserved_disjoint_canonicalRoundingCore W₂)
      (canonicalRoundingCore_subset_core W₁)
      (canonicalRoundingCore_subset_core W₂) width width hwidth hwidth
      hcoreBound₁ hcoreBound₂ (by simp) (by simp) herror₁ herror₂
      (D.scaledForwardCoefficient scale) (D.scaledReverseCoefficient scale)
      E.commonCenter W₁.translatePoint W₂.translatePoint hp₁ hp₂
      E.forwardZeroCoordinateCenterError E.reverseZeroCoordinateCenterError
      hcenter₁ hcenter₂ hq₁ hq₂ S.progression B E.translate₁ (-E.translate₂)
      gamma hcontain₁ hcontain₂ hbox hvolume₁ hvolume₂ hgamma
      (by simpa only [W₁] using hfull₁) (by simpa only [W₂] using hfull₂)
      (by simpa only [HighCoefficientSideSelectionData.commonCoveringRadius,
        W₁, W₂, S, core₁, core₂, scale] using hthick₁)
      (by simpa only [HighCoefficientSideSelectionData.commonCoveringRadius,
        W₁, W₂, S, core₁, core₂, scale] using hthick₂)

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
