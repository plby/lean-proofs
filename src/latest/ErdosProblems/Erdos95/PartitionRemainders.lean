/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.PruneAdmissible

/-!
# Pointwise decomposition after one partitioning step
-/

namespace Erdos95.PartitionRemainders

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionCells
open Erdos95.PartitionBookkeeping Erdos95.PartitionStep
open Erdos95.RichPointCombinatorics Erdos95.SurfacePruning
open Erdos95.SurfaceFactors Erdos95.GuthStructure

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

/-- Non-bad sign cells. -/
noncomputable def goodSigns (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact Finset.univ.filter fun sign ↦ sign ∉ badSigns L S p c

theorem mem_goodSigns_iff {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c : ℕ} {sign : Fin J → Bool} :
    sign ∈ goodSigns L S p c ↔ sign ∉ badSigns L S p c := by
  classical
  simp [goodSigns]

/-- Good cells to which the line-family induction applies. -/
noncomputable def lowSigns (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact (goodSigns L S p c).filter fun sign ↦
    r ^ 2 ≤ 4 * (cellLines L S p sign).card

/-- Good cells in the elementary large-richness range. -/
noncomputable def highSigns (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact (goodSigns L S p c).filter fun sign ↦
    4 * (cellLines L S p sign).card < r ^ 2

theorem mem_lowSigns_iff {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c r : ℕ} {sign : Fin J → Bool} :
    sign ∈ lowSigns L S p c r ↔
      sign ∈ goodSigns L S p c ∧
        r ^ 2 ≤ 4 * (cellLines L S p sign).card := by
  classical
  simp [lowSigns]

theorem mem_highSigns_iff {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c r : ℕ} {sign : Fin J → Bool} :
    sign ∈ highSigns L S p c r ↔
      sign ∈ goodSigns L S p c ∧
        4 * (cellLines L S p sign).card < r ^ 2 := by
  classical
  simp [highSigns]

theorem mem_lowSigns_or_mem_highSigns_of_good
    {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c r : ℕ} {sign : Fin J → Bool}
    (hsign : sign ∈ goodSigns L S p c) :
    sign ∈ lowSigns L S p c r ∨ sign ∈ highSigns L S p c r := by
  by_cases hlow : r ^ 2 ≤ 4 * (cellLines L S p sign).card
  · exact Or.inl (mem_lowSigns_iff.mpr ⟨hsign, hlow⟩)
  · exact Or.inr (mem_highSigns_iff.mpr
      ⟨hsign, Nat.lt_of_not_ge hlow⟩)

/-- Union of the inductive residuals in the low cells. -/
noncomputable def lowResidualPoints
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) : Finset Space := by
  classical
  exact (lowSigns L S p c r).biUnion fun sign ↦
    residualRichPoints (cellLines L S p sign) (cellF sign) r

/-- Rich points in high cells, controlled by the elementary overlap lemma. -/
noncomputable def highCellRichPoints
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ) : Finset Space := by
  classical
  exact (highSigns L S p c r).biUnion fun sign ↦
    signCell S p sign ∩ richPoints (cellLines L S p sign) r

/-- Wall points not rich in the line family of an irreducible wall factor. -/
noncomputable def wallRemainder
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (r : ℕ) : Finset Space := by
  classical
  exact wallPoints S p \
    surfaceRichPoints L (irreducibleFactors (partitionPolynomial p))
      (reducedRichness r)

/-- The temporary collection before root-threshold pruning. -/
noncomputable def temporarySurfaces
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) : Finset Poly3 := by
  classical
  exact F₀ ∪ (lowSigns L S p c r).biUnion cellF ∪
    irreducibleFactors (partitionPolynomial p)

/-- Pointwise decomposition of a residual set after pruning. -/
theorem subset_partition_remainders
    {L : Finset LineIndex} {S : Finset Space} {J : ℕ}
    {p : Fin J → Poly3} {c r A : ℕ} (hr : 2 ≤ r)
    (F₀ : Finset Poly3)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hSrich : S ⊆ richPoints L r)
    (havoid : ∀ x ∈ S,
      x ∉ surfaceRichPoints L
        (largeSurfaces L
          (temporarySurfaces F₀ L S p c r cellF) A)
        (reducedRichness r)) :
    S ⊆
      badCellPoints L S p c ∪
      lowResidualPoints L S p c r cellF ∪
      highCellRichPoints L S p c r ∪
      wallRemainder L S p r ∪
      surfaceRichPoints L
        (smallSurfaces L
          (temporarySurfaces F₀ L S p c r cellF) A)
        (reducedRichness r) := by
  classical
  intro x hxS
  have hxrich : x ∈ richPoints L r := hSrich hxS
  rcases mem_wallPoints_or_exists_mem_signCell hxS with hxwall | ⟨sign, hxcell⟩
  · by_cases hxFactor : x ∈
        surfaceRichPoints L (irreducibleFactors (partitionPolynomial p))
          (reducedRichness r)
    · obtain ⟨Q, hQfac, hxQ⟩ := mem_surfaceRichPoints_iff.mp hxFactor
      have hQtemp : Q ∈ temporarySurfaces F₀ L S p c r cellF := by
        simp [temporarySurfaces, hQfac]
      rcases Finset.mem_union.mp
            (surfaces_subset_large_union_small L
            (temporarySurfaces F₀ L S p c r cellF) A hQtemp) with
        hQlarge | hQsmall
      · exact (havoid x hxS
          (mem_surfaceRichPoints_iff.mpr ⟨Q, hQlarge, hxQ⟩)).elim
      · exact Finset.mem_union_right _
          (mem_surfaceRichPoints_iff.mpr ⟨Q, hQsmall, hxQ⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hxwall, hxFactor⟩))
  · by_cases hbad : sign ∈ badSigns L S p c
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
          (mem_badCellPoints_iff.mpr ⟨sign, hbad, hxcell⟩))))
    · have hgood : sign ∈ goodSigns L S p c :=
        mem_goodSigns_iff.mpr hbad
      rcases mem_lowSigns_or_mem_highSigns_of_good (r := r) hgood with
          hlow | hhigh
      · have hxCellRich := mem_richPoints_cellLines_of_mem hr hxcell hxrich
        by_cases hxSurf : x ∈ surfaceRichPoints
            (cellLines L S p sign) (cellF sign) (reducedRichness r)
        · obtain ⟨Q, hQcell, hxQ⟩ := mem_surfaceRichPoints_iff.mp hxSurf
          have hQtemp : Q ∈ temporarySurfaces F₀ L S p c r cellF := by
            unfold temporarySurfaces
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨sign, hlow, hQcell⟩))
          have hsurfaceMono : surfaceLines (cellLines L S p sign) Q ⊆
              surfaceLines L Q :=
            surfaceLines_mono (cellLines_subset L S p sign) Q
          have hxQroot : x ∈ richPoints (surfaceLines L Q)
              (reducedRichness r) :=
            richPoints_mono_family hsurfaceMono _ hxQ
          rcases Finset.mem_union.mp
              (surfaces_subset_large_union_small L
                (temporarySurfaces F₀ L S p c r cellF) A hQtemp) with
            hQlarge | hQsmall
          · exact (havoid x hxS
              (mem_surfaceRichPoints_iff.mpr
                ⟨Q, hQlarge, hxQroot⟩)).elim
          · exact Finset.mem_union_right _
              (mem_surfaceRichPoints_iff.mpr
                ⟨Q, hQsmall, hxQroot⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.mpr
                ⟨sign, hlow, mem_residualRichPoints_iff.mpr
                  ⟨hxCellRich, hxSurf⟩⟩))))
      · have hxCellRich := mem_richPoints_cellLines_of_mem hr hxcell hxrich
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨sign, hhigh, Finset.mem_inter.mpr
              ⟨hxcell, hxCellRich⟩⟩)))

end Erdos95.PartitionRemainders
