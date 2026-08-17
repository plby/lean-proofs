/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.SpecialFamily

/-!
# Elementary facts for one polynomial-partitioning step

These lemmas connect a rich point in a strict sign cell with the line
subfamily entering that cell.  They deliberately make no estimates; the
cardinality bookkeeping is kept separate from the geometry.
-/

namespace Erdos95.PartitionStep

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines
open Erdos95.RichPointCombinatorics Erdos95.SurfacePruning

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

theorem cellLines_subset (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) (sign : Fin J → Bool) :
    cellLines L S p sign ⊆ L := by
  intro l hl
  exact (mem_cellLines_iff.mp hl).1

theorem linesThrough_subset_cellLines_of_mem_signCell
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    (hx : x ∈ signCell S p sign) :
    linesThrough L x ⊆ cellLines L S p sign := by
  intro l hl
  have hldata := mem_linesThrough_iff.mp hl
  exact mem_cellLines_iff.mpr ⟨hldata.1, x, hx, hldata.2⟩

theorem linesThrough_mono_cellLines_of_mem_signCell
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    (hx : x ∈ signCell S p sign) :
    linesThrough L x ⊆ linesThrough (cellLines L S p sign) x := by
  intro l hl
  exact mem_linesThrough_iff.mpr
    ⟨linesThrough_subset_cellLines_of_mem_signCell hx hl,
      (mem_linesThrough_iff.mp hl).2⟩

theorem mem_intersectionPoints_cellLines_of_mem
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    {r : ℕ} (hr : 2 ≤ r) (hxcell : x ∈ signCell S p sign)
    (hxrich : x ∈ richPoints L r) :
    x ∈ intersectionPoints (cellLines L S p sign) := by
  classical
  have hxdata := mem_richPoints_iff.mp hxrich
  have hsub :=
    linesThrough_subset_cellLines_of_mem_signCell (L := L) hxcell
  have htwo : 2 ≤ (linesThrough L x).card := hr.trans hxdata.2
  obtain ⟨l, m, hl, hm, hlm⟩ := Finset.one_lt_card_iff.mp (by omega :
    1 < (linesThrough L x).card)
  unfold intersectionPoints
  apply Finset.mem_image.mpr
  refine ⟨(l, m), ?_, ?_⟩
  · unfold intersectingPairs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hsub hl, hsub hm⟩, hlm, ?_⟩
    exact ⟨x, (mem_linesThrough_iff.mp hl).2,
      (mem_linesThrough_iff.mp hm).2⟩
  · apply intersection_unique hlm
    · exact pairIntersection_on_first ⟨x,
        (mem_linesThrough_iff.mp hl).2, (mem_linesThrough_iff.mp hm).2⟩
    · exact pairIntersection_on_second ⟨x,
        (mem_linesThrough_iff.mp hl).2, (mem_linesThrough_iff.mp hm).2⟩
    · exact (mem_linesThrough_iff.mp hl).2
    · exact (mem_linesThrough_iff.mp hm).2

/-- A rich point lying in a strict cell remains rich for the subfamily of
lines which enters that cell. -/
theorem mem_richPoints_cellLines_of_mem
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    {r : ℕ} (hr : 2 ≤ r) (hxcell : x ∈ signCell S p sign)
    (hxrich : x ∈ richPoints L r) :
    x ∈ richPoints (cellLines L S p sign) r := by
  apply mem_richPoints_iff.mpr
  refine ⟨mem_intersectionPoints_cellLines_of_mem hr hxcell hxrich, ?_⟩
  exact (mem_richPoints_iff.mp hxrich).2.trans
    (Finset.card_le_card
      (linesThrough_mono_cellLines_of_mem_signCell (L := L) hxcell))

/-- Root-rich points accounted for only by surfaces discarded at threshold
`A` have a uniform ordered-pair bound. -/
theorem root_pair_mul_card_small_surfaceRichPoints_le
    (L : Finset LineIndex) (F : Finset Poly3) (A r : ℕ) (hr : 2 ≤ r) :
    r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (GuthStructure.reducedRichness r)).card ≤
      8 * (F.card * A ^ 2) := by
  have hpair := GuthStructure.richness_pair_le_eight_reduced_pair hr
  have hgeneric := richness_mul_pred_mul_card_surfaceRichPoints_le
    L (smallSurfaces L F A) (GuthStructure.reducedRichness r)
  calc
    r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (GuthStructure.reducedRichness r)).card ≤
        8 * (GuthStructure.reducedRichness r *
          (GuthStructure.reducedRichness r - 1)) *
          (surfaceRichPoints L (smallSurfaces L F A)
            (GuthStructure.reducedRichness r)).card := by
      gcongr
    _ = 8 * ((GuthStructure.reducedRichness r *
          (GuthStructure.reducedRichness r - 1)) *
          (surfaceRichPoints L (smallSurfaces L F A)
            (GuthStructure.reducedRichness r)).card) := by ring
    _ ≤ 8 *
        ∑ Q ∈ smallSurfaces L F A, (surfaceLines L Q).card ^ 2 := by
      gcongr
    _ ≤ 8 * (F.card * A ^ 2) := by
      gcongr
      exact sum_sq_surfaceLines_small_le L F A

end Erdos95.PartitionStep
