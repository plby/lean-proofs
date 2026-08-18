/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientSelectionPackage
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientCenterError
import ErdosProblems.Erdos186.PZ.Intersection.SourceReverseControl
import ErdosProblems.Erdos186.PZ.Intersection.AnisotropicAdjugateCapacityPos
import ErdosProblems.Erdos186.PZ.Intersection.AnisotropicCanonicalPostCFPAssembly

/-!
# Post-CFP assembly from the high-coefficient source selections

This file fixes all finite objects in the PZ intersection construction.  It
uses the canonical high-coefficient side selections, negates the second CFP
witness, chooses the canonical rounding cores, absorbs anisotropic rounding
errors in the full covered dilates, and proves the common-centre and
full-rank lattice fields.  The only geometric inputs left are the two literal
centered-zonotope thickness inclusions.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Scale the capped coefficients so that their upper bound becomes one
half, exactly as required by the centred-zonotope translation lemma. -/
def highCoefficientZonotopeScale {d : ℕ}
    {A : Finset (LatticePoint d)} {a₀ : realImage A}
    {c : realImage A → ℝ} {mu : ℝ}
    (_D : ConvexPoolsData A a₀ c mu) : ℝ :=
  mu * (A.card : ℝ) / 2

/-- Transport an enhanced witness across equality of its finite input. -/
def transportEnhancedCFPWitness
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (h : X = Y) (W : CFP.EnhancedCFPWitness X s D k loss) :
    CFP.EnhancedCFPWitness Y s D k loss := by
  subst Y
  exact W

@[simp] theorem transportEnhancedCFPWitness_rank
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (h : X = Y) (W : CFP.EnhancedCFPWitness X s D k loss) :
    (transportEnhancedCFPWitness h W).rank = W.rank := by
  subst Y
  rfl

/-- The selected progression carrier is unchanged by input transport. -/
@[simp] theorem transportEnhancedCFPWitness_progression_carrier
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (h : X = Y) (W : CFP.EnhancedCFPWitness X s D k loss) :
    (transportEnhancedCFPWitness h W).progression.carrier =
      W.progression.carrier := by
  subst Y
  rfl

/-- The selected progression volume is unchanged by input transport. -/
@[simp] theorem transportEnhancedCFPWitness_progression_volume
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (h : X = Y) (W : CFP.EnhancedCFPWitness X s D k loss) :
    (transportEnhancedCFPWitness h W).progression.volume =
      W.progression.volume := by
  subst Y
  rfl

namespace HighCoefficientSideSelectionData

variable {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu theta gamma : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}

/-- The forward side witness, with its input rewritten as the oriented
deviation pool used by equation (15). -/
def forwardWitness
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    CFP.EnhancedCFPWitness
      (orientedTranslate .forward D.a (D.largeA₁ theta))
      E.side₁.reserveBound E.side₁.rankBound E.side₁.dilation
      E.side₁.loss :=
  transportEnhancedCFPWitness
    (orientedTranslate_forward_eq_identifiedTranslate
      D.a (D.largeA₁ theta)).symm E.side₁.witness

/-- The reverse side witness obtained by negating the selected witness on
`A₂ - a`. -/
def reverseWitness
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    CFP.EnhancedCFPWitness
      (orientedTranslate .reverse D.a (D.largeA₂ theta))
      E.side₂.reserveBound E.side₂.rankBound E.side₂.dilation
      E.side₂.loss :=
  transportEnhancedCFPWitness
    (orientedTranslate_reverse_eq_image_neg_identifiedTranslate
      D.a (D.largeA₂ theta)).symm
    (negateEnhancedCFPWitness E.side₂.witness)

theorem forwardWitness_rank
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.forwardWitness.rank = (selector.chosen A hA).dimension := by
  change E.side₁.witness.rank = (selector.chosen A hA).dimension
  exact E.dimension₁

theorem forwardWitness_progression_carrier
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.forwardWitness.progression.carrier = E.side₁.progression.carrier := by
  simp only [forwardWitness, transportEnhancedCFPWitness_progression_carrier]

theorem forwardWitness_progression_volume
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.forwardWitness.progression.volume = E.side₁.progression.volume := by
  simp only [forwardWitness, transportEnhancedCFPWitness_progression_volume]

theorem reverseWitness_rank
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.reverseWitness.rank = (selector.chosen A hA).dimension := by
  simpa only [reverseWitness, transportEnhancedCFPWitness_rank,
    negateEnhancedCFPWitness.rank] using E.dimension₂

theorem reverseWitness_progression_carrier
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.reverseWitness.progression.carrier =
      E.side₂.progression.carrier.image (fun x ↦ -x) := by
  simp only [reverseWitness, transportEnhancedCFPWitness_progression_carrier,
    negateEnhancedCFPWitness.progression]
  exact negatedGAP.carrier E.side₂.progression

theorem reverseWitness_progression_volume
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    E.reverseWitness.progression.volume = E.side₂.progression.volume := by
  simp only [reverseWitness, transportEnhancedCFPWitness_progression_volume,
    negateEnhancedCFPWitness.progression]
  exact negatedGAP.volume E.side₂.progression

/-- Canonical forward rounding core. -/
abbrev forwardRoundingCore
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :=
  canonicalRoundingCore E.forwardWitness

/-- Canonical reverse rounding core. -/
abbrev reverseRoundingCore
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :=
  canonicalRoundingCore E.reverseWitness

/-- The common full balanced center, before the low-coefficient and CFP
discard errors are paid. -/
def commonCenter
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    Fin (selector.chosen A hA).dimension → ℝ :=
  zonotopeCenter (orientedTranslate .forward D.a D.A₁)
    (D.scaledForwardCoefficient (highCoefficientZonotopeScale D))

/-- Forward centre error: low-coefficient omission plus the exact CFP
discard/reserve/translation budget. -/
def forwardCenterError
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) : ℝ :=
  let S := selector.chosen A hA
  let scale := highCoefficientZonotopeScale D
  (S.identifiedCore.card : ℝ) * scale * theta *
      (sourceCoordinateWidth S.progression : ℝ) +
    ((((E.side₁.loss + E.side₁.reserveBound : ℕ) : ℝ) *
        ((1 : ℝ) / 2 * (sourceCoordinateWidth S.progression : ℝ))) +
      (E.side₁.reserveBound : ℝ) *
        (sourceCoordinateWidth S.progression : ℝ))

/-- Reverse centre error with the unchanged numerical parameters of the
negated witness. -/
def reverseCenterError
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) : ℝ :=
  let S := selector.chosen A hA
  let scale := highCoefficientZonotopeScale D
  (S.identifiedCore.card : ℝ) * scale * theta *
      (sourceCoordinateWidth S.progression : ℝ) +
    ((((E.side₂.loss + E.side₂.reserveBound : ℕ) : ℝ) *
        ((1 : ℝ) / 2 * (sourceCoordinateWidth S.progression : ℝ))) +
      (E.side₂.reserveBound : ℝ) *
        (sourceCoordinateWidth S.progression : ℝ))

/-- The determinant-power radius of the two canonical side lattices. -/
def commonCoveringRadius
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) : ℕ :=
  let r := (selector.chosen A hA).dimension
  (stepMatrix (rankCastGAP E.forwardWitness.progression
      E.forwardWitness_rank)).det.natAbs ^ r *
    (stepMatrix (rankCastGAP E.reverseWitness.progression
      E.reverseWitness_rank)).det.natAbs ^ r

end HighCoefficientSideSelectionData

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

theorem highCoefficientZonotopeScale_nonneg
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu) :
    0 ≤ highCoefficientZonotopeScale D := by
  unfold highCoefficientZonotopeScale
  positivity

theorem highCoefficientZonotopeScale_mul_cap
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu) :
    highCoefficientZonotopeScale D * (mu * A.card)⁻¹ = (1 : ℝ) / 2 := by
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨D.a, D.a_mem⟩)
  have hne : mu * (A.card : ℝ) ≠ 0 := (mul_pos hmu hcard).ne'
  unfold highCoefficientZonotopeScale
  field_simp

end ConvexPoolsData

namespace Theorem4PostCFPData

/-- The complete finite post-CFP construction from a packaged pair of
high-coefficient side selections.  Full rank and anisotropic residual
absorption are derived internally from the two displayed scalar hierarchies.
Only the two final centered-zonotope thickness inclusions remain geometric
inputs. -/
def ofHighCoefficientSideSelection
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu theta gamma : ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (E : HighCoefficientSideSelectionData selector hA D theta gamma)
    (hr : 0 < (selector.chosen A hA).dimension)
    (hmu : 0 < mu) (htheta : 0 ≤ theta) (hgamma : 0 < gamma)
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
      Real.sqrt (((((selector.chosen A hA).dimension *
          E.forwardRoundingCore.card : ℕ)) : ℝ)) *
        (((((selector.chosen A hA).dimension.factorial *
          (2 * sourceControlScale selector hA) ^
            ((selector.chosen A hA).dimension - 1) *
          3 ^ (selector.chosen A hA).dimension : ℕ)) : ℝ)) ≤
        gamma * E.side₁.dilation)
    (hanisotropic₂ :
      Real.sqrt (((((selector.chosen A hA).dimension *
          E.reverseRoundingCore.card : ℕ)) : ℝ)) *
        (((((selector.chosen A hA).dimension.factorial *
          (2 * sourceControlScale selector hA) ^
            ((selector.chosen A hA).dimension - 1) *
          3 ^ (selector.chosen A hA).dimension : ℕ)) : ℝ)) ≤
        gamma * E.side₂.dilation)
    (hthick₁ : ∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) + E.forwardCenterError) →
      y ∈ centeredZonotope E.forwardRoundingCore
        (D.scaledForwardCoefficient (highCoefficientZonotopeScale D)))
    (hthick₂ : ∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) + E.reverseCenterError) →
      y ∈ centeredZonotope E.reverseRoundingCore
        (D.scaledReverseCoefficient (highCoefficientZonotopeScale D))) :
    Theorem4PostCFPData (selector.chosen A hA).identifiedCore := by
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
  have hscale : 0 ≤ scale := by
    exact D.highCoefficientZonotopeScale_nonneg hmu
  have hhalf : scale * (mu * S.identifiedCore.card)⁻¹ = (1 : ℝ) / 2 := by
    exact D.highCoefficientZonotopeScale_mul_cap hmu
  have haBox : D.a ∈ (gapCoefficientBox S.progression).carrier :=
    S.identifiedCore_subset_coefficientBox D.a_mem
  have hH₁box : D.largeA₁ theta ⊆
      (gapCoefficientBox S.progression).carrier :=
    (D.largeA₁_subset theta).trans
      ((D.A₁_subset_erase.trans (Finset.erase_subset _ _)).trans
        S.identifiedCore_subset_coefficientBox)
  have hH₂box : D.largeA₂ theta ⊆
      (gapCoefficientBox S.progression).carrier :=
    (D.largeA₂_subset theta).trans
      ((D.A₂_subset_erase.trans (Finset.erase_subset _ _)).trans
        S.identifiedCore_subset_coefficientBox)
  have hA₁ : D.largeA₁ theta ⊆ S.identifiedCore.erase D.a :=
    (D.largeA₁_subset theta).trans D.A₁_subset_erase
  have hA₂ : D.largeA₂ theta ⊆ S.identifiedCore.erase D.a :=
    (D.largeA₂_subset theta).trans D.A₂_subset_erase
  have hdisjoint : Disjoint (D.largeA₁ theta) (D.largeA₂ theta) :=
    D.disjoint.mono (D.largeA₁_subset theta) (D.largeA₂_subset theta)
  have hrank₁ : W₁.rank = S.dimension := by
    exact E.forwardWitness_rank
  have hrank₂ : W₂.rank = S.dimension := by
    exact E.reverseWitness_rank
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
        ((S.progression.widths i - 1 : ℕ) : ℝ) := by
      exact_mod_cast hb
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
        ((S.progression.widths i - 1 : ℕ) : ℝ) := by
      exact_mod_cast hb
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
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((S.dimension * core₁.card : ℕ) : ℝ)) * width i) →
      e ∈ (W₁.progression.dilate E.side₁.dilation).carrier := by
    apply enhancedWitness_anisotropic_errorBox_of_sourceControlBox_pos
      hr W₁ hrank₁ S.progression m hm E.translate₁ hcentered₁
      (by simpa only [rankCastGAP_carrier] using hcontain₁)
      gamma (Real.sqrt (((S.dimension * core₁.card : ℕ) : ℝ)))
      hgamma (Real.sqrt_nonneg _) (by simpa only [rankCastGAP_volume] using hvolume₁)
      hdet₁
    simpa only [S, core₁, W₁, width] using hanisotropic₁
  have herror₂ : ∀ e : LatticePoint S.dimension,
      e ∈ gapStepLattice W₂.progression →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((S.dimension * core₂.card : ℕ) : ℝ)) * width i) →
      e ∈ (W₂.progression.dilate E.side₂.dilation).carrier := by
    apply enhancedWitness_anisotropic_errorBox_of_sourceControlBox_pos
      hr W₂ hrank₂ S.progression m hm (-E.translate₂) hcentered₂
      (by simpa only [rankCastGAP_carrier] using hcontain₂)
      gamma (Real.sqrt (((S.dimension * core₂.card : ℕ) : ℝ)))
      hgamma (Real.sqrt_nonneg _) (by simpa only [rankCastGAP_volume] using hvolume₂)
      hdet₂
    simpa only [S, core₂, W₂, width] using hanisotropic₂
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
        E.forwardCenterError := by
    intro i
    simpa only [HighCoefficientSideSelectionData.commonCenter,
      HighCoefficientSideSelectionData.forwardCenterError, S, scale, W₁, core₁]
      using D.fullBalancedCenter_forwardOriented_center_error S.progression
        S.identifiedCore_subset_coefficientBox htheta hscale hhalf.le
        W₁ i
  have hcenter₂ : ∀ i,
      |E.commonCenter i -
        (realVector W₂.translatePoint +
          zonotopeCenter core₂ (D.scaledReverseCoefficient scale)) i| ≤
        E.reverseCenterError := by
    intro i
    simpa only [HighCoefficientSideSelectionData.commonCenter,
      HighCoefficientSideSelectionData.reverseCenterError, S, scale, W₂, core₂]
      using D.fullBalancedCenter_reverseOriented_center_error S.progression
        S.identifiedCore_subset_coefficientBox htheta hscale hhalf.le
        W₂ i
  exact ofCanonicalTargets_controlledBoxGammaHierarchy_anisotropic_pos
    hr D.a_mem hA₁ hA₂ hdisjoint W₁ W₂ hrank₁ hrank₂
    core₁ core₂ (reserved_disjoint_canonicalRoundingCore W₁)
    (reserved_disjoint_canonicalRoundingCore W₂)
    (canonicalRoundingCore_subset_core W₁)
    (canonicalRoundingCore_subset_core W₂) width width hwidth hwidth
    hcoreBound₁ hcoreBound₂ (by simp) (by simp) herror₁ herror₂
    (D.scaledForwardCoefficient scale) (D.scaledReverseCoefficient scale)
    E.commonCenter W₁.translatePoint W₂.translatePoint hp₁ hp₂
    E.forwardCenterError E.reverseCenterError hcenter₁ hcenter₂ hq₁ hq₂
    S.progression B E.translate₁ (-E.translate₂) gamma hcontain₁ hcontain₂
    hbox hvolume₁ hvolume₂ hgamma
    (by simpa only [W₁] using hfull₁) (by simpa only [W₂] using hfull₂)
    (by simpa only [HighCoefficientSideSelectionData.commonCoveringRadius,
      W₁, W₂, S, core₁, core₂, scale] using hthick₁)
    (by simpa only [HighCoefficientSideSelectionData.commonCoveringRadius,
      W₁, W₂, S, core₁, core₂, scale] using hthick₂)

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
