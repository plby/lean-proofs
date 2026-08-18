/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.CanonicalScale
import ErdosProblems.Erdos186.PZ.Reduction.NoDimensionIncrease

/-!
# Eligibility of dense coordinate candidates

This file packages a selected progression's centered difference carrier as
an actual integer box.  It then turns the two numerical guards needed in
Lemma 10--a canonical-scale threshold and a difference-box cardinal bound--
into `CandidateClosedAt` for the strong-scale selector.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

namespace GAP

/-- The centered integer box having the widths of a coefficient difference
GAP. -/
def differenceIntegerBox {d r : ℕ} (P : Erdos186.GAP d r) :
    CFP.IntegerBox r where
  lower i := -((P.widths i : ℤ) - 1)
  upper i := (P.widths i : ℤ) - 1

@[simp] theorem mem_differenceIntegerBox_iff {d r : ℕ}
    (P : Erdos186.GAP d r) (x : LatticePoint r) :
    x ∈ (differenceIntegerBox P).carrier ↔
      ∀ i, -((P.widths i : ℤ) - 1) ≤ x i ∧
        x i ≤ (P.widths i : ℤ) - 1 := by
  simp [differenceIntegerBox, CFP.IntegerBox.mem_carrier_iff]

/-- The box is exactly the carrier of the standard difference-coordinate
GAP. -/
@[simp] theorem differenceIntegerBox_carrier {d r : ℕ}
    (P : Erdos186.GAP d r) :
    (differenceIntegerBox P).carrier =
      (differenceCoefficientGAP P).carrier := by
  ext x
  rw [mem_differenceIntegerBox_iff]
  have hOne : (differenceCoefficientGAP P).dilate 1 =
      differenceCoefficientGAP P := by
    rw [Erdos186.GAP.mk.injEq]
    refine ⟨?_, rfl, ?_⟩
    · funext j
      simp [Erdos186.GAP.dilate]
    · funext i
      simp only [Erdos186.GAP.dilate_widths, one_mul]
      have hi := (differenceCoefficientGAP P).width_pos i
      omega
  rw [← hOne]
  rw [GAP.mem_dilate_differenceCoefficientGAP_iff]
  constructor <;> intro h i
  · have hi := h i
    simp only [one_mul]
    rw [Nat.cast_sub (P.width_pos i)]
    simpa using hi
  · have hi := h i
    simp only [one_mul] at hi
    rw [Nat.cast_sub (P.width_pos i)] at hi
    simpa using hi

/-- The difference box costs at most `2^rank` times the displayed
progression volume. -/
theorem differenceIntegerBox_card_le {d r : ℕ}
    (P : Erdos186.GAP d r) :
    (differenceIntegerBox P).carrier.card ≤ 2 ^ r * P.volume := by
  rw [differenceIntegerBox_carrier]
  exact (Erdos186.GAP.card_carrier_le_volume
    (differenceCoefficientGAP P)).trans
    (differenceCoefficientGAP_volume_le P)

end GAP

/-- Every translated coordinate candidate is contained in the explicit
difference integer box. -/
theorem candidate_subset_differenceIntegerBox
    {d : ℕ} {A : Finset (LatticePoint d)}
    (S : SelectedCFP A)
    (X : Finset (BoxPoint S.dimension))
    (hX : X ⊆ S.identifiedCore)
    (x : BoxPoint S.dimension)
    (hx : x ∈ (gapCoefficientBox S.progression).carrier) :
    identifiedTranslate X x ⊆
      (GAP.differenceIntegerBox S.progression).carrier := by
  rw [GAP.differenceIntegerBox_carrier]
  exact GAP.translate_subset_differenceCoefficientGAP S.progression
    (hX.trans S.identifiedCore_subset_coefficientBox) hx

/-- The canonical scale and a difference-box cardinal guard construct a
strong-scale eligible input for one candidate. -/
theorem scaleSelector_candidate_eligible
    {β η exponent : ℝ} {C : HigherDimensionalContext β η}
    {d : ℕ} {A : Finset (LatticePoint d)}
    (S : SelectedCFP A)
    (X : Finset (BoxPoint S.dimension))
    (hX : X ⊆ S.identifiedCore) (hXne : X.Nonempty)
    (x : BoxPoint S.dimension)
    (hx : x ∈ (gapCoefficientBox S.progression).carrier)
    (hη : Real.rpow (X.card : ℝ) η ≤
      (canonicalScale C S.dimension X.card : ℝ))
    (hexponent : Real.rpow (X.card : ℝ) exponent ≤
      (canonicalScale C S.dimension X.card : ℝ))
    (hupper : (C.scaleDen S.dimension : ℝ) *
        (canonicalScale C S.dimension X.card : ℝ) *
          Real.logb 2 (X.card : ℝ) ≤
        (C.scaleNum S.dimension : ℝ) * (X.card : ℝ))
    (hbox : (2 : ℝ) ^ S.dimension * (S.progression.volume : ℝ) ≤
      Real.rpow (X.card : ℝ) β) :
    (C.scaleSelector exponent).Eligible (identifiedTranslate X x) := by
  let I : EligibleInput C (identifiedTranslate X x) := {
    box := GAP.differenceIntegerBox S.progression
    scale := canonicalScale C S.dimension X.card
    nonempty := identifiedTranslate_nonempty hXne x
    subset_box := candidate_subset_differenceIntegerBox S X hX x hx
    box_card_le := by
      rw [card_identifiedTranslate]
      have hc :
          ((GAP.differenceIntegerBox S.progression).carrier.card : ℝ) ≤
            (2 : ℝ) ^ S.dimension * (S.progression.volume : ℝ) := by
        exact_mod_cast GAP.differenceIntegerBox_card_le S.progression
      exact hc.trans hbox
    scale_lower := by simpa using hη
    scale_upper := by simpa using hupper }
  apply C.scaleSelector_eligible_of_input I
  · change canonicalScale C S.dimension X.card =
      canonicalScale C S.dimension (identifiedTranslate X x).card
    rw [card_identifiedTranslate]
  · simpa using hexponent

/-- Guarded terminal closure: if every dense candidate passes one canonical
scale threshold and its difference box fits beneath the CFP power, then the
strong-scale selector is locally closed at the current state. -/
theorem scaleSelector_candidateClosedAt_of_threshold
    {β η exponent δ : ℝ} {C : HigherDimensionalContext β η}
    {d : ℕ} {A : Finset (LatticePoint d)}
    {hA : (C.scaleSelector exponent).Eligible A}
    {threshold : ℕ}
    (hscale : ∀ m : ℕ, threshold ≤ m →
      Real.rpow (m : ℝ) η ≤
          (canonicalScale C
            ((C.scaleSelector exponent).chosen A hA).dimension m : ℝ) ∧
      Real.rpow (m : ℝ) exponent ≤
          (canonicalScale C
            ((C.scaleSelector exponent).chosen A hA).dimension m : ℝ) ∧
      (C.scaleDen ((C.scaleSelector exponent).chosen A hA).dimension : ℝ) *
          (canonicalScale C
            ((C.scaleSelector exponent).chosen A hA).dimension m : ℝ) *
            Real.logb 2 (m : ℝ) ≤
        (C.scaleNum ((C.scaleSelector exponent).chosen A hA).dimension : ℝ) *
          (m : ℝ))
    (hcard : ∀ (X : Finset
        (BoxPoint ((C.scaleSelector exponent).chosen A hA).dimension)),
      X ⊆ ((C.scaleSelector exponent).chosen A hA).identifiedCore →
      X.Nonempty → δ * (A.card : ℝ) ≤ (X.card : ℝ) →
      threshold ≤ X.card)
    (hbox : ∀ (X : Finset
        (BoxPoint ((C.scaleSelector exponent).chosen A hA).dimension)),
      X ⊆ ((C.scaleSelector exponent).chosen A hA).identifiedCore →
      X.Nonempty → δ * (A.card : ℝ) ≤ (X.card : ℝ) →
      (2 : ℝ) ^ ((C.scaleSelector exponent).chosen A hA).dimension *
        (((C.scaleSelector exponent).chosen A hA).progression.volume : ℝ) ≤
          Real.rpow (X.card : ℝ) β) :
    (C.scaleSelector exponent).CandidateClosedAt A hA δ := by
  intro X hX hXne hdense x hx
  have hs := hscale X.card (hcard X hX hXne hdense)
  exact scaleSelector_candidate_eligible
    ((C.scaleSelector exponent).chosen A hA) X hX hXne x hx
      hs.1 hs.2.1 hs.2.2 (hbox X hX hXne hdense)

end

end Erdos186.PZ.Reduction
