/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoxWeightedFunctionalSlab
import ErdosProblems.Erdos186.PZ.Intersection.SourceControlConvexBody

/-!
# Source slab cardinality with anisotropic box normalization

This is the width-preserving form of the source slab theorem.  The dual
functional mass uses the actual side lengths of the source control box.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Public source control box used by both the John argument and the
anisotropic dual norm. -/
def sourceFunctionalControlBox
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (hA : selector.Eligible A) : IntegerBox
      (selector.chosen A hA).dimension :=
  publicControlIntegerBox (selector.chosen A hA).progression
    (2 * context.scaleDen (selector.chosen A hA).dimension)

/-- The selected canonical core has at most `slab` points in every narrow
slab normalized by the source control box. -/
theorem exists_boxWeightedSourceFunctionalSlabCardinalityConstants
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (hA : selector.Eligible A)
    (hd : 0 < (selector.chosen A hA).dimension) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {delta gamma : ℝ}
        (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
          delta gamma)
        (hclosed : selector.CandidateClosedAt A hA delta)
        (hgamma : 0 < gamma)
        (X : Finset (LatticePoint (selector.chosen A hA).dimension))
        (hX : X ⊆ (selector.chosen A hA).identifiedCore)
        (a : LatticePoint (selector.chosen A hA).dimension)
        (ha : a ∈ (gapCoefficientBox
          (selector.chosen A hA).progression).carrier)
        {s D k loss : ℕ}
        (W : CFP.EnhancedCFPWitness
          (Reduction.identifiedTranslate X a) s D k loss)
        (f : (Fin (selector.chosen A hA).dimension → ℝ) →L[ℝ] ℝ)
        (t gamma' : ℝ) (slab : ℕ),
        gamma' = gamma → f ≠ 0 → 0 < t →
        delta * (A.card : ℝ) ≤ (slab : ℝ) →
        1 ≤ (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
          ((controlIntegerBox (selector.chosen A hA).progression
            (2 * context.scaleDen
              (selector.chosen A hA).dimension)).carrier.card : ℝ) →
        (∀ (Z : Finset
            (LatticePoint (selector.chosen A hA).dimension))
          (hZ : selector.Eligible Z),
          delta * (A.card : ℝ) ≤ (Z.card : ℝ) →
          (2 : ℝ) ^ (selector.chosen A hA).dimension *
              (2 * (context.scaleDen
                (selector.chosen A hA).dimension : ℝ)) ^
                  (selector.chosen A hA).dimension *
              (3 : ℝ) ^ (selector.chosen A hA).dimension * constant *
              (((2 * context.scaleDen
                  (selector.chosen A hA).dimension + 1) ^
                    (selector.chosen A hA).dimension *
                  2 ^ (selector.chosen A hA).dimension : ℕ) : ℝ) <
            ((selector.chosen Z hZ).dilation : ℝ) * gamma) →
        (2 : ℝ) ^ (selector.chosen A hA).dimension *
              (2 * (context.scaleDen
                (selector.chosen A hA).dimension : ℝ)) ^
                  (selector.chosen A hA).dimension *
              (3 : ℝ) ^ (selector.chosen A hA).dimension * constant *
              (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
              (((2 * context.scaleDen
                  (selector.chosen A hA).dimension + 1) ^
                    (selector.chosen A hA).dimension *
                  2 ^ (selector.chosen A hA).dimension : ℕ) : ℝ) <
            gamma →
        ((canonicalRoundingCore W).filter fun x ↦
          |f (realVector x)| <
            t * boxCoefficientMass
              (sourceFunctionalControlBox selector hA) f).card ≤ slab := by
  obtain ⟨factorBound, constant, hconstant, hcontradiction⟩ :=
    exists_boxWeightedFunctionalSlabContradictionConstants
      (selector.chosen A hA).dimension hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma hirr hclosed hgamma X hX a ha s D k loss W f t gamma'
    slab hgamma' hf ht hdenseSlab hscale hlow hfull
  subst gamma'
  let S := selector.chosen A hA
  let m : ℕ := 2 * context.scaleDen S.dimension
  let B : IntegerBox S.dimension := publicControlIntegerBox S.progression m
  let boxFactor : ℕ := (m + 1) ^ S.dimension * 2 ^ S.dimension
  let Z : Finset (LatticePoint S.dimension) :=
    (canonicalRoundingCore W).filter fun x ↦
      |f (realVector x)| < t * boxCoefficientMass B f
  by_contra hcard
  have hslabLt : slab < Z.card := Nat.lt_of_not_ge hcard
  have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
  have hZsubInput : Z ⊆ Reduction.identifiedTranslate X a := by
    intro z hz
    exact W.core_subset
      (canonicalRoundingCore_subset_core W (Finset.mem_filter.mp hz).1)
  have hdenseZ : delta * (A.card : ℝ) ≤ (Z.card : ℝ) := by
    exact hdenseSlab.trans (by exact_mod_cast (Nat.le_of_lt hslabLt))
  obtain ⟨hZ, hTdimension, hTvolume⟩ :=
    exists_selectedWitness_of_dense_subset_identifiedTranslate selector hirr
      hclosed X (by simpa only [S] using hX) a
      (by simpa only [S] using ha) Z hZsubInput hZne hdenseZ
  let T := selector.chosen Z hZ
  have hXbox : X ⊆ (gapCoefficientBox S.progression).carrier :=
    hX.trans S.identifiedCore_subset_coefficientBox
  have hinputDifference : Reduction.identifiedTranslate X a ⊆
      (Reduction.GAP.differenceCoefficientGAP S.progression).carrier :=
    Reduction.GAP.translate_subset_differenceCoefficientGAP
      S.progression hXbox (by simpa only [S] using ha)
  have hTcoreB : T.witness.core ⊆ B.carrier := by
    intro z hz
    have hzZ : z ∈ Z := T.witness.core_subset hz
    have hzDifference : z ∈
        (Reduction.GAP.differenceCoefficientGAP S.progression).carrier :=
      hinputDifference (hZsubInput hzZ)
    rw [IntegerBox.mem_carrier_iff]
    intro i
    have habs := abs_coordinate_le_width_sub_one_of_mem_difference
      S.progression z hzDifference i
    have hmOne : 1 ≤ m := by
      dsimp only [m]
      have hden := context.scaleDen_pos S.dimension
      omega
    have hradiusNat : S.progression.widths i - 1 ≤
        m * (S.progression.widths i - 1) := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (S.progression.widths i - 1) hmOne
    have hradiusInt : ((S.progression.widths i - 1 : ℕ) : ℤ) ≤
        ((m * (S.progression.widths i - 1) : ℕ) : ℤ) := by
      exact_mod_cast hradiusNat
    have habs' := abs_le.mp habs
    change -((m * (S.progression.widths i - 1) : ℕ) : ℤ) ≤ z i ∧
      z i ≤ ((m * (S.progression.widths i - 1) : ℕ) : ℤ)
    exact ⟨(neg_le_neg hradiusInt).trans habs'.1,
      habs'.2.trans hradiusInt⟩
  have hTcoreSlab : ∀ z ∈ T.witness.core,
      |f (realVector z)| < t * boxCoefficientMass B f := by
    intro z hz
    exact (Finset.mem_filter.mp (T.witness.core_subset hz)).2
  have hBbody : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B) := by
    apply isConvexBody_boxRealization_publicControlIntegerBox
    · dsimp only [m]
      exact Nat.mul_pos (by omega) (context.scaleDen_pos S.dimension)
    · intro i
      exact (S.witness.three_le_width i).trans' (by omega)
  have hzeroB : (0 : LatticePoint S.dimension) ∈ B.carrier :=
    zero_mem_publicControlIntegerBox S.progression m
  have hbox : B.carrier.card ≤ boxFactor * S.progression.volume := by
    simpa only [B, boxFactor, m, publicControlIntegerBox_carrier] using
      controlIntegerBox_card_le S.progression m
  have hlowT := hlow Z hZ hdenseZ
  have hTscaleDen : T.witness.scaleDen = context.scaleDen S.dimension := by
    dsimp only [T, S, Reduction.BoundedCFPSelector.chosen]
    exact (selector.input Z hZ).selectedCFP_scaleDen
  apply hcontradiction T.witness B f t gamma
  · simpa only [T, S] using hTdimension
  · exact hBbody
  · exact hf
  · exact ht
  · exact hzeroB
  · exact hTcoreB
  · exact hTcoreSlab
  · simpa only [B, m, publicControlIntegerBox_carrier] using hscale
  · exact hbox
  · exact S.progression.volume_pos
  · exact hgamma
  · simpa only [T, S] using hTvolume
  · rw [hTscaleDen]
    simpa only [T, S, m, boxFactor,
      Reduction.BoundedCFPSelector.chosen] using hlowT
  · rw [hTscaleDen]
    simpa only [T, S, m, boxFactor,
      Reduction.BoundedCFPSelector.chosen] using hfull

end

end Erdos186.PZ.Intersection
