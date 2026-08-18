/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ControlledSideSelection
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionContainment

/-!
# Source-controlled balanced side selection

The fixed control box in Lemma 11 is not additional data: it is the
`2 * scaleDen` dilation of the reference coefficient-difference GAP.  This
file specializes the balanced side-selection argument to that box and also
exports its explicit cardinal cost.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Core retention and bounded irreducibility select both balanced sides in
one fixed source-defined integer box.  The final conjunct is the exact box
cardinality factor consumed by the projection-cardinality full-rank proof. -/
theorem exists_balanced_side_selections_with_sourceControlBox
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hdelta : 0 < delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ)) :
    let S := selector.chosen A hA
    let m := 2 * context.scaleDen S.dimension
    let B := controlIntegerBox S.progression m
    let Q := (m + 1) ^ S.dimension * 2 ^ S.dimension
    ∃ h₁ : selector.Eligible (Reduction.identifiedTranslate D.A₁ D.a),
      ∃ h₂ : selector.Eligible (Reduction.identifiedTranslate D.A₂ D.a),
        let T₁ := selector.chosen
          (Reduction.identifiedTranslate D.A₁ D.a) h₁
        let T₂ := selector.chosen
          (Reduction.identifiedTranslate D.A₂ D.a) h₂
        T₁.dimension = S.dimension ∧
          T₂.dimension = S.dimension ∧
          gamma * (S.progression.volume : ℝ) ≤
            (T₁.progression.volume : ℝ) ∧
          gamma * (S.progression.volume : ℝ) ≤
            (T₂.progression.volume : ℝ) ∧
          (∃ t, T₁.progression.carrier ⊆ CFP.translate t B.carrier) ∧
          (∃ t, T₂.progression.carrier ⊆ CFP.translate t B.carrier) ∧
          B.carrier.card ≤ Q * S.progression.volume := by
  let S := selector.chosen A hA
  let m := 2 * context.scaleDen S.dimension
  let B := controlIntegerBox S.progression m
  let Q := (m + 1) ^ S.dimension * 2 ^ S.dimension
  have hA₁sub : D.A₁ ⊆ S.identifiedCore :=
    D.A₁_subset_erase.trans (Finset.erase_subset _ _)
  have hA₂sub : D.A₂ ⊆ S.identifiedCore :=
    D.A₂_subset_erase.trans (Finset.erase_subset _ _)
  have hdense₁ : delta * (A.card : ℝ) ≤ (D.A₁.card : ℝ) :=
    hcoreRetention.trans (by exact_mod_cast D.card_lower_A₁)
  have hdense₂ : delta * (A.card : ℝ) ≤ (D.A₂.card : ℝ) :=
    hcoreRetention.trans (by exact_mod_cast D.card_lower_A₂)
  have hpopulation : (0 : ℝ) < A.card := by
    exact_mod_cast (selector.eligible_nonempty hA).card_pos
  have hA₁ne : D.A₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hle : delta * (A.card : ℝ) ≤ 0 := by
      simpa [hzero] using hdense₁
    exact (not_le_of_gt (mul_pos hdelta hpopulation)) hle
  have hA₂ne : D.A₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hle : delta * (A.card : ℝ) ≤ 0 := by
      simpa [hzero] using hdense₂
    exact (not_le_of_gt (mul_pos hdelta hpopulation)) hle
  have haBox : D.a ∈ (gapCoefficientBox S.progression).carrier :=
    S.identifiedCore_subset_coefficientBox D.a_mem
  let h₁ : selector.Eligible (Reduction.identifiedTranslate D.A₁ D.a) :=
    hclosed D.A₁ hA₁sub hA₁ne hdense₁ D.a haBox
  let h₂ : selector.Eligible (Reduction.identifiedTranslate D.A₂ D.a) :=
    hclosed D.A₂ hA₂sub hA₂ne hdense₂ D.a haBox
  have hcontrolled : BoundedCoordinateBoundingSetsControlled selector A hA
      delta B.carrier := by
    simpa only [B, m, S] using
      boundedCoordinateBoundingSetsControlled_of_enhancedCFP selector delta
  have hout₁ := lemma11_of_boundedCoordinateIrreducible selector hA hirr
    hcontrolled D.A₁ hA₁sub hA₁ne hdense₁ D.a haBox h₁
  have hout₂ := lemma11_of_boundedCoordinateIrreducible selector hA hirr
    hcontrolled D.A₂ hA₂sub hA₂ne hdense₂ D.a haBox h₂
  have hcard : B.carrier.card ≤ Q * S.progression.volume := by
    simpa only [B, Q, m] using
      controlIntegerBox_card_le S.progression m
  refine ⟨h₁, h₂, hout₁.1, hout₂.1, hout₁.2.1, hout₂.2.1, ?_, ?_,
    hcard⟩
  · obtain ⟨t, ht⟩ := hout₁.2.2
    exact ⟨t, by simpa only [pzTranslate_eq_cfpTranslate] using ht⟩
  · obtain ⟨t, ht⟩ := hout₂.2.2
    exact ⟨t, by simpa only [pzTranslate_eq_cfpTranslate] using ht⟩

end

end Erdos186.PZ.Intersection
