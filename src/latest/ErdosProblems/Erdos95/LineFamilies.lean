/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.CellLines

/-!
# Finite families of Elekes--Sharir lines

The incidence induction is most naturally stated for an arbitrary subfamily
of the full `P × P` line family.  This file supplies the corresponding finite
rich-point and algebraic-surface definitions.
-/

namespace Erdos95.LineFamilies

open Erdos95.Algebraic Erdos95.ES

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Ordered pairs of distinct intersecting lines from `L`. -/
noncomputable def intersectingPairs (L : Finset LineIndex) :
    Finset (LineIndex × LineIndex) := by
  classical
  exact (L.product L).filter fun z ↦
    z.1 ≠ z.2 ∧ Intersects z.1.1 z.1.2 z.2.1 z.2.2

/-- The unique intersection point of an incident ordered pair. -/
noncomputable def pairIntersection (z : LineIndex × LineIndex) : Space3 := by
  classical
  exact if h : Intersects z.1.1 z.1.2 z.2.1 z.2.2 then
    Classical.choose h
  else 0

theorem pairIntersection_on_first {z : LineIndex × LineIndex}
    (hz : Intersects z.1.1 z.1.2 z.2.1 z.2.2) :
    OnLine z.1.1 z.1.2 (pairIntersection z) := by
  classical
  simp only [pairIntersection, dif_pos hz]
  exact (Classical.choose_spec hz).1

theorem pairIntersection_on_second {z : LineIndex × LineIndex}
    (hz : Intersects z.1.1 z.1.2 z.2.1 z.2.2) :
    OnLine z.2.1 z.2.2 (pairIntersection z) := by
  classical
  simp only [pairIntersection, dif_pos hz]
  exact (Classical.choose_spec hz).2

/-- Lines of a subfamily passing through `x`. -/
noncomputable def linesThrough (L : Finset LineIndex) (x : Space3) :
    Finset LineIndex := by
  classical
  exact L.filter fun l ↦ OnLine l.1 l.2 x

theorem mem_linesThrough_iff {L : Finset LineIndex} {x : Space3}
    {l : LineIndex} :
    l ∈ linesThrough L x ↔ l ∈ L ∧ OnLine l.1 l.2 x := by
  classical
  simp [linesThrough]

theorem linesThrough_mono {L M : Finset LineIndex} (hLM : L ⊆ M)
    (x : Space3) : linesThrough L x ⊆ linesThrough M x := by
  intro l hl
  exact mem_linesThrough_iff.mpr
    ⟨hLM (mem_linesThrough_iff.mp hl).1, (mem_linesThrough_iff.mp hl).2⟩

theorem card_linesThrough_le (L : Finset LineIndex) (x : Space3) :
    (linesThrough L x).card ≤ L.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Actual intersection points of distinct lines in `L`. -/
noncomputable def intersectionPoints (L : Finset LineIndex) : Finset Space3 :=
  (intersectingPairs L).image pairIntersection

/-- Intersection points incident to at least `r` lines of `L`. -/
noncomputable def richPoints (L : Finset LineIndex) (r : ℕ) : Finset Space3 := by
  classical
  exact (intersectionPoints L).filter fun x ↦ r ≤ (linesThrough L x).card

theorem mem_richPoints_iff {L : Finset LineIndex} {r : ℕ} {x : Space3} :
    x ∈ richPoints L r ↔
      x ∈ intersectionPoints L ∧ r ≤ (linesThrough L x).card := by
  classical
  simp [richPoints]

theorem richPoints_mono_family {L M : Finset LineIndex} (hLM : L ⊆ M)
    (r : ℕ) : richPoints L r ⊆ richPoints M r := by
  classical
  intro x hx
  have hxdata := mem_richPoints_iff.mp hx
  have hcard := Finset.card_le_card (linesThrough_mono hLM x)
  have hxinter : x ∈ intersectionPoints M := by
    unfold intersectionPoints at hxdata ⊢
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hxdata.1
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    unfold intersectingPairs at hz ⊢
    have hzdata := Finset.mem_filter.mp hz
    have hzmem := Finset.mem_product.mp hzdata.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hLM hzmem.1, hLM hzmem.2⟩, hzdata.2⟩
  exact mem_richPoints_iff.mpr ⟨hxinter, hxdata.2.trans hcard⟩

theorem richPoints_antitone_richness (L : Finset LineIndex)
    {r s : ℕ} (hrs : r ≤ s) : richPoints L s ⊆ richPoints L r := by
  intro x hx
  have h := mem_richPoints_iff.mp hx
  exact mem_richPoints_iff.mpr ⟨h.1, hrs.trans h.2⟩

theorem pairIntersection_fiber (L : Finset LineIndex) (x : Space3) :
    (intersectingPairs L).filter (fun z ↦ pairIntersection z = x) =
      (linesThrough L x).offDiag := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨hz, hzx⟩
    have hzdata := Finset.mem_filter.mp hz
    have hzmem := Finset.mem_product.mp hzdata.1
    refine ⟨mem_linesThrough_iff.mpr ⟨hzmem.1, ?_⟩,
      mem_linesThrough_iff.mpr ⟨hzmem.2, ?_⟩, hzdata.2.1⟩
    · rw [← hzx]
      exact pairIntersection_on_first hzdata.2.2
    · rw [← hzx]
      exact pairIntersection_on_second hzdata.2.2
  · rintro ⟨hz₁, hz₂, hne⟩
    have hint : Intersects z.1.1 z.1.2 z.2.1 z.2.2 :=
      ⟨x, (mem_linesThrough_iff.mp hz₁).2,
        (mem_linesThrough_iff.mp hz₂).2⟩
    have hzmem : z ∈ intersectingPairs L := by
      unfold intersectingPairs
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_linesThrough_iff.mp hz₁).1,
          (mem_linesThrough_iff.mp hz₂).1⟩, hne, hint⟩
    refine ⟨hzmem, ?_⟩
    exact intersection_unique hne
      (pairIntersection_on_first hint) (pairIntersection_on_second hint)
      (mem_linesThrough_iff.mp hz₁).2 (mem_linesThrough_iff.mp hz₂).2

theorem card_intersectingPairs_eq_sum (L : Finset LineIndex) :
    (intersectingPairs L).card =
      ∑ x ∈ intersectionPoints L,
        (linesThrough L x).card * ((linesThrough L x).card - 1) := by
  classical
  rw [Finset.card_eq_sum_card_image pairIntersection (intersectingPairs L)]
  change _ = ∑ x ∈ (intersectingPairs L).image pairIntersection, _
  apply Finset.sum_congr rfl
  intro x hx
  rw [pairIntersection_fiber, Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Each `r`-rich point accounts for at least `r(r-1)` ordered pairs. -/
theorem richness_mul_pred_mul_card_le_intersectingPairs
    (L : Finset LineIndex) (r : ℕ) :
    r * (r - 1) * (richPoints L r).card ≤ (intersectingPairs L).card := by
  classical
  rw [card_intersectingPairs_eq_sum]
  calc
    r * (r - 1) * (richPoints L r).card =
        ∑ x ∈ richPoints L r, r * (r - 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ richPoints L r,
        (linesThrough L x).card * ((linesThrough L x).card - 1) := by
      apply Finset.sum_le_sum
      intro x hx
      have hr := (mem_richPoints_iff.mp hx).2
      exact Nat.mul_le_mul hr (Nat.sub_le_sub_right hr 1)
    _ ≤ ∑ x ∈ intersectionPoints L,
        (linesThrough L x).card * ((linesThrough L x).card - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro x hx hnot
        omega

theorem card_intersectingPairs_le_sq (L : Finset LineIndex) :
    (intersectingPairs L).card ≤ L.card ^ 2 := by
  classical
  calc
    (intersectingPairs L).card ≤ (L.product L).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = L.card ^ 2 := by simp [pow_two]

/-- The elementary universal rich-point estimate. -/
theorem richness_mul_pred_mul_card_le_sq (L : Finset LineIndex) (r : ℕ) :
    r * (r - 1) * (richPoints L r).card ≤ L.card ^ 2 :=
  (richness_mul_pred_mul_card_le_intersectingPairs L r).trans
    (card_intersectingPairs_le_sq L)

/-- Lines of `L` contained in the algebraic surface `Z(Q)`. -/
noncomputable def surfaceLines (L : Finset LineIndex) (Q : Poly3) :
    Finset LineIndex := by
  classical
  exact L.filter fun l ↦ LineContained Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

theorem mem_surfaceLines_iff {L : Finset LineIndex} {Q : Poly3}
    {l : LineIndex} :
    l ∈ surfaceLines L Q ↔ l ∈ L ∧ LineContained Q
      (linePoint l.1 l.2 0) (lineDirection l.1 l.2) := by
  classical
  simp [surfaceLines]

theorem surfaceLines_subset (L : Finset LineIndex) (Q : Poly3) :
    surfaceLines L Q ⊆ L := by
  classical
  exact Finset.filter_subset _ _

theorem surfaceLines_mono {L M : Finset LineIndex} (hLM : L ⊆ M)
    (Q : Poly3) : surfaceLines L Q ⊆ surfaceLines M Q := by
  classical
  intro l hl
  have h := mem_surfaceLines_iff.mp hl
  exact mem_surfaceLines_iff.mpr ⟨hLM h.1, h.2⟩

end Erdos95.LineFamilies
