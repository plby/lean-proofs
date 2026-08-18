/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientSideSelection

/-!
# Packaged high-coefficient side selections

The source selection theorem is existential because eligibility of the two
translated candidates is a proposition.  Downstream geometric formulae need
to refer to the selected witnesses, their translations, and the common
control box.  This file packages those choices without adding any new
hypothesis and provides one canonical classical choice of the package.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The fixed dilation used for the source control box. -/
def sourceControlScale {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (selector : Reduction.BoundedCFPSelector context)
    (hA : selector.Eligible A) : ℕ :=
  2 * context.scaleDen (selector.chosen A hA).dimension

/-- The explicit cardinal multiplier of the source control box. -/
def sourceControlCardMultiplier {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (selector : Reduction.BoundedCFPSelector context)
    (hA : selector.Eligible A) : ℕ :=
  let S := selector.chosen A hA
  let m := sourceControlScale selector hA
  (m + 1) ^ S.dimension * 2 ^ S.dimension

/-- All deterministic output of Lemma 11 for the two high-coefficient
candidate pools. -/
structure HighCoefficientSideSelectionData
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (hA : selector.Eligible A)
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu : ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (theta gamma : ℝ) where
  eligible₁ : selector.Eligible
    (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
  eligible₂ : selector.Eligible
    (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
  dimension₁ :
    (selector.chosen
      (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
      eligible₁).dimension = (selector.chosen A hA).dimension
  dimension₂ :
    (selector.chosen
      (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
      eligible₂).dimension = (selector.chosen A hA).dimension
  volume₁ : gamma * ((selector.chosen A hA).progression.volume : ℝ) ≤
    ((selector.chosen
      (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
      eligible₁).progression.volume : ℝ)
  volume₂ : gamma * ((selector.chosen A hA).progression.volume : ℝ) ≤
    ((selector.chosen
      (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
      eligible₂).progression.volume : ℝ)
  translate₁ : LatticePoint (selector.chosen A hA).dimension
  translate₂ : LatticePoint (selector.chosen A hA).dimension
  contained₁ :
    (selector.chosen
      (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
      eligible₁).progression.carrier ⊆
      CFP.translate translate₁
        (controlIntegerBox (selector.chosen A hA).progression
          (sourceControlScale selector hA)).carrier
  contained₂ :
    (selector.chosen
      (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
      eligible₂).progression.carrier ⊆
      CFP.translate translate₂
        (controlIntegerBox (selector.chosen A hA).progression
          (sourceControlScale selector hA)).carrier
  controlBox_card :
    (controlIntegerBox (selector.chosen A hA).progression
      (sourceControlScale selector hA)).carrier.card ≤
      sourceControlCardMultiplier selector hA *
        (selector.chosen A hA).progression.volume

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

/-- The selected forward-side CFP object. -/
abbrev side₁
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :=
  selector.chosen
    (Reduction.identifiedTranslate (D.largeA₁ theta) D.a) E.eligible₁

/-- The selected (pre-negation) reverse-side CFP object. -/
abbrev side₂
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :=
  selector.chosen
    (Reduction.identifiedTranslate (D.largeA₂ theta) D.a) E.eligible₂

end HighCoefficientSideSelectionData

/-- The high-coefficient side-selection theorem in packaged form. -/
theorem nonempty_highCoefficientSideSelectionData
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {delta gamma mu theta : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hdelta : 0 < delta) (htheta : 0 ≤ theta)
    (hcap : 0 < (mu * (selector.chosen A hA).identifiedCore.card)⁻¹)
    (hmassBudget :
      (A.card : ℝ) * theta +
          delta * (A.card : ℝ) *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ <
        (1 - 2 *
          (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2) :
    Nonempty (HighCoefficientSideSelectionData selector hA D theta gamma) := by
  let S := selector.chosen A hA
  let m := sourceControlScale selector hA
  let B := controlIntegerBox S.progression m
  let Q := sourceControlCardMultiplier selector hA
  obtain ⟨h₁, h₂, hdim₁, hdim₂, hvol₁, hvol₂,
      ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hbox⟩ :=
    exists_highCoefficient_side_selections_with_sourceControlBox selector D
      hirr hclosed hdelta htheta hcap hmassBudget
  refine ⟨{
    eligible₁ := h₁
    eligible₂ := h₂
    dimension₁ := hdim₁
    dimension₂ := hdim₂
    volume₁ := hvol₁
    volume₂ := hvol₂
    translate₁ := t₁
    translate₂ := t₂
    contained₁ := ?_
    contained₂ := ?_
    controlBox_card := ?_ }⟩
  · simpa only [S, m, B, sourceControlScale] using ht₁
  · simpa only [S, m, B, sourceControlScale] using ht₂
  · simpa only [S, m, B, Q, sourceControlScale,
      sourceControlCardMultiplier] using hbox

/-- A canonical choice of both high-coefficient side selections. -/
noncomputable def chooseHighCoefficientSideSelectionData
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {delta gamma mu theta : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hdelta : 0 < delta) (htheta : 0 ≤ theta)
    (hcap : 0 < (mu * (selector.chosen A hA).identifiedCore.card)⁻¹)
    (hmassBudget :
      (A.card : ℝ) * theta +
          delta * (A.card : ℝ) *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ <
        (1 - 2 *
          (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2) :
    HighCoefficientSideSelectionData selector hA D theta gamma :=
  Classical.choice (nonempty_highCoefficientSideSelectionData selector D
    hirr hclosed hdelta htheta hcap hmassBudget)

end

end Erdos186.PZ.Intersection
