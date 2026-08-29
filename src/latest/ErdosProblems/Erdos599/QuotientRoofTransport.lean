/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CommonQuotient

/-!
# Transporting roofs through the common quotient

This file records the ambient-web roof statements hidden by the dependent
casts in `waveToLargerQuotient`.  They are the form of Lemma 3.30 needed in
the Section 6 closing-up argument: a point roofed by a stage wave remains
roofed after moving that wave to the raw-union quotient and after taking the
countable up-arrow there.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Terminal vertices are unchanged when a wave is transported along an
equality of webs.  Keeping this elementary dependent-cast lemma explicit
avoids unfolding equality recursors in the quotient constructions below. -/
theorem terminalFrontier_castWebWave {H K : DWeb V} (h : H = K)
    (W : H.Wave) :
    K.terminalFrontier (h ▸ W).1 = H.terminalFrontier W.1 := by
  cases h
  rfl

/-- Vertex sets are likewise invariant under transport along an equality of
webs. -/
theorem vertexSet_castWebWave {H K : DWeb V} (h : H = K)
    (W : H.Wave) :
    K.vertexSet (h ▸ W).1 = H.vertexSet W.1 := by
  cases h
  rfl

/-- A member of a wave cast along a web equality has a preimage with the
same support. -/
theorem exists_preimage_castWebWave {H K : DWeb V} (h : H = K)
    (W : H.Wave) {p : K.DPath} (hp : p ∈ (h ▸ W).1) :
    ∃ q ∈ W.1, p.support = q.support := by
  subst K
  exact ⟨p, hp, rfl⟩

/-- Quotient transport introduces no vertex except vertices of the old wave
and essential vertices of the larger commitment set. -/
theorem vertexSet_waveToLargerQuotient_subset
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    (G.quotient Y).vertexSet
        (G.waveToLargerQuotient hNoEnter hXY W).1 ⊆
      (G.quotient X).vertexSet W.1 ∪ Y := by
  let H := G.quotient X
  let Z : ((G.quotient X).quotient Y).Wave :=
    ⟨(G.quotient X).generalWaveQuotient Y W.1,
      (G.quotient X).isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have heq : (G.quotient X).quotient Y = G.quotient Y := by
    calc
      (G.quotient X).quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport : G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  rw [htransport, vertexSet_castWebWave heq Z]
  rw [show Z.1 = (G.quotient X).generalWaveQuotient Y W.1 by rfl]
  rw [generalWaveQuotient,
    (G.quotient X).vertexSet_admissibleWarpQuotient]
  apply Set.union_subset
  · exact ((G.quotient X).vertexSet_terminalSuffixFamily_subset Y W.1).trans
      Set.subset_union_left
  · intro z hz
    exact Or.inr hz.1

/-- If a transported path contains a vertex outside the larger commitment
set, then its whole support comes from one old path.  This same-path form is
the support fact needed by the Section 6 closing recurrence. -/
theorem exists_old_path_of_mem_waveToLargerQuotient_of_not_mem
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave)
    {p : (G.quotient Y).DPath}
    (hp : p ∈ (G.waveToLargerQuotient hNoEnter hXY W).1)
    {z : V} (hzp : z ∈ p.support) (hzY : z ∉ Y) :
    ∃ q ∈ W.1, p.support ⊆ q.support := by
  let H := G.quotient X
  let Z : ((G.quotient X).quotient Y).Wave :=
    ⟨(G.quotient X).generalWaveQuotient Y W.1,
      (G.quotient X).isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have heq : (G.quotient X).quotient Y = G.quotient Y := by
    calc
      (G.quotient X).quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport : G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  rw [htransport] at hp
  obtain ⟨p₀, hp₀, hsupp⟩ := exists_preimage_castWebWave heq Z hp
  have hzp₀ : z ∈ p₀.support := hsupp ▸ hzp
  change p₀ ∈ (G.quotient X).generalWaveQuotient Y W.1 at hp₀
  unfold generalWaveQuotient admissibleWarpQuotient at hp₀
  rcases hp₀ with hp₀ | hp₀
  · obtain ⟨r, hr⟩ := hp₀
    have hp₀eq : p₀ = (G.quotient X).restrictPathToQuotient Y r.1
        ((G.quotient X).pathQuotientAdmissible_terminalSuffixFamily Y W.1
          r.1 r.2) := hr
    obtain ⟨q, hqW, _hqfin, hrq⟩ := r.2
    refine ⟨Sum.inl q, hqW, ?_⟩
    intro v hvp
    have hvp₀ : v ∈ p₀.support := hsupp.symm ▸ hvp
    rw [hp₀eq, (G.quotient X).support_restrictPathToQuotient] at hvp₀
    rw [hrq] at hvp₀
    exact (G.quotient X).terminalRoofSuffix_support_subset Y q hvp₀
  · obtain ⟨e, he, hp₀eq⟩ := hp₀
    subst p₀
    have hze : z = e := by simpa using hzp₀
    exact (hzY (hze ▸ he.1.1)).elim

/-- A quotient wave roofs the essential commitment frontier in the ambient
web.  Unlike the earlier disjoint-source interface, this form uses the
general quotient-source formula and therefore needs no assumption that the
old source is disjoint from the commitment set. -/
theorem essential_subset_original_roof_of_quotient_wave_general
    {X : Set V} {W : Set (G.quotient X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hW : (G.quotient X).IsWave W) :
    G.essential X ⊆ G.roof ((G.quotient X).terminalFrontier W) := by
  intro x hx p hp
  have hmeetX : G.Meets p X :=
    ⟨p.start, p.start_mem_support, hp.1 ▸ hx.1⟩
  let hm : p.walk.Meets X :=
    ⟨hmeetX.choose, hmeetX.choose_spec.1, hmeetX.choose_spec.2⟩
  let L := p.walk.lastHit X hm
  have hLEss : L.startpoint ∈ G.essential X :=
    G.lastHit_mem_essential X p hp hmeetX
  have hLSource : L.startpoint ∈ (G.quotient X).source := by
    rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hNoEnter]
    exact ⟨Or.inr hLEss.1, fun hStrict ↦ hStrict.2 hLEss⟩
  obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
    G.exists_quotientPath_from_lastHit X p hp hmeetX
  have hqTarget : (G.quotient X).IsTargetPathFrom L.startpoint q :=
    ⟨hqStart, hqFinish ▸ hp.2⟩
  obtain ⟨y, hyq, hyW⟩ := hW.2.2 hLSource q hqTarget
  have hyL : y ∈ L.walk.support := by
    rw [hqSupport] at hyq
    exact hyq
  exact ⟨y, L.support_subset hyL, hyW⟩

/-- Every point roofed by the terminal frontier of a quotient wave in the
quotient is roofed by the same frontier in the ambient web. -/
theorem quotientWave_roof_subset_original_roof_general
    {X : Set V} {W : Set (G.quotient X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hW : (G.quotient X).IsWave W) :
    (G.quotient X).roof ((G.quotient X).terminalFrontier W) ⊆
      G.roof ((G.quotient X).terminalFrontier W) := by
  let S := (G.quotient X).terminalFrontier W
  have hEss : G.essential X ⊆ G.roof S := by
    simpa only [S] using
      G.essential_subset_original_roof_of_quotient_wave_general hNoEnter hW
  have hRoofX : G.roof X ⊆ G.roof S := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  intro v hv
  by_cases hvStrict : v ∈ G.strictRoof X
  · exact hRoofX hvStrict.1
  · exact G.quotient_roof_subset_original_roof_of_essential X S hEss
      ⟨hv, hvStrict⟩

/-- Quotienting a wave once more does not lose any part of its old ambient
roof.  Both roofs in this statement are evaluated in the web before the
second quotient. -/
theorem roof_terminalFrontier_subset_generalWaveQuotient
    {X : Set V} {U : Set G.DPath}
    (hNoEnter : G.NoEdgeEnters G.source) (hU : G.IsWave U) :
    G.roof (G.terminalFrontier U) ⊆
      G.roof ((G.quotient X).terminalFrontier
        (G.generalWaveQuotient X U)) := by
  let Q : (G.quotient X).Wave :=
    ⟨G.generalWaveQuotient X U,
      G.isWave_generalWaveQuotient hNoEnter hU⟩
  let S := (G.quotient X).terminalFrontier Q.1
  have hEss : G.essential X ⊆ G.roof S := by
    simpa only [S, Q] using
      G.essential_subset_original_roof_of_quotient_wave_general
        hNoEnter Q.2
  have hRoofX : G.roof X ⊆ G.roof S := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  intro v hv
  by_cases hvStrict : v ∈ G.strictRoof X
  · exact hRoofX hvStrict.1
  · have hvQ : v ∈ (G.quotient X).roof S := by
      apply (G.quotient X).roof_mono ?_
      · simpa only [S, Q] using
          (G.roof_sdiff_strictRoof_subset_quotient_roof X
            (G.terminalFrontier U) ⟨hv, hvStrict⟩)
      · intro z hz
        dsimp only [S, Q]
        rw [G.terminalFrontier_generalWaveQuotient]
        exact Or.inl hz
    exact G.quotientWave_roof_subset_original_roof_general
      hNoEnter Q.2 hvQ

/-- Moving a wave from `G / X` to `G / Y`, for `X ⊆ Y`, preserves its
terminal roof when both terminal frontiers are interpreted in the original
web `G`. -/
theorem roof_terminalFrontier_subset_waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    G.roof ((G.quotient X).terminalFrontier W.1) ⊆
      G.roof ((G.quotient Y).terminalFrontier
        (G.waveToLargerQuotient hNoEnter hXY W).1) := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    ⟨H.generalWaveQuotient Y W.1,
      H.isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  let Q := G.waveToLargerQuotient hNoEnter hXY W
  let S := (G.quotient Y).terminalFrontier Q.1
  have hQZ : Q = heq ▸ Z := by
    apply Subtype.ext
    simp only [Q, waveToLargerQuotient, H, Z]
  have hEssY : G.essential Y ⊆ G.roof S := by
    simpa only [S, Q] using
      G.essential_subset_original_roof_of_quotient_wave_general
        hNoEnter Q.2
  have hRoofY : G.roof Y ⊆ G.roof S := by
    rw [← G.roof_essential Y]
    exact G.roof_cut hEssY
  have hEssX : G.essential X ⊆ G.roof S := by
    exact (G.essential_subset X).trans
      ((G.subset_roof X).trans ((G.roof_mono hXY).trans hRoofY))
  intro v hv
  by_cases hvStrict : v ∈ G.strictRoof X
  · exact hRoofY (G.roof_mono hXY hvStrict.1)
  · have hvH0 : v ∈ H.roof
        ((G.quotient X).terminalFrontier W.1 \
          G.strictRoof X) := by
      simpa only [H] using
        (G.roof_sdiff_strictRoof_subset_quotient_roof X
          ((G.quotient X).terminalFrontier W.1) ⟨hv, hvStrict⟩)
    have hvH : v ∈ H.roof ((G.quotient X).terminalFrontier W.1) :=
      H.roof_mono Set.sdiff_subset hvH0
    have hvZ : v ∈ H.roof ((H.quotient Y).terminalFrontier Z.1) := by
      exact H.roof_terminalFrontier_subset_generalWaveQuotient
        hNoEnter.quotient W.2 hvH
    have hvQ : v ∈ (G.quotient X).roof S := by
      change v ∈ (G.quotient X).roof
        ((G.quotient Y).terminalFrontier Q.1)
      rw [hQZ]
      rw [terminalFrontier_castWebWave heq Z]
      exact hvZ
    exact G.quotient_roof_subset_original_roof_of_essential X S hEssX
      ⟨hvQ, hvStrict⟩

/-- In particular, every point in the old strict roof is in the new
ambient roof after quotient transport.  No essential-frontier disjointness
is needed for this roof-valued conclusion. -/
theorem strictRoof_terminalFrontier_subset_roof_waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    G.strictRoof ((G.quotient X).terminalFrontier W.1) ⊆
      G.roof ((G.quotient Y).terminalFrontier
        (G.waveToLargerQuotient hNoEnter hXY W).1) :=
  (G.strictRoof_subset_roof _).trans
    (G.roof_terminalFrontier_subset_waveToLargerQuotient
      hNoEnter hXY W)

/-- Strict-roof preservation by quotient transport, under its exact
additional ambient essential-frontier disjointness condition. -/
theorem strictRoof_terminalFrontier_subset_waveToLargerQuotient_of_disjoint
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave)
    (hDisjoint : Disjoint
      (G.essential ((G.quotient Y).terminalFrontier
        (G.waveToLargerQuotient hNoEnter hXY W).1))
      (G.strictRoof ((G.quotient X).terminalFrontier W.1))) :
    G.strictRoof ((G.quotient X).terminalFrontier W.1) ⊆
      G.strictRoof ((G.quotient Y).terminalFrontier
        (G.waveToLargerQuotient hNoEnter hXY W).1) :=
  by
    intro v hv
    exact ⟨G.roof_terminalFrontier_subset_waveToLargerQuotient
      hNoEnter hXY W hv.1,
      fun hvEss ↦ Set.disjoint_left.1 hDisjoint hvEss hv⟩

/-- Roof order between two waves in the same quotient lifts to roof order
in the original web. -/
theorem original_roofLE_of_quotient_roofLE
    (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    {U W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W)
    (hUW : (G.quotient X).RoofLE U W) :
    G.roof ((G.quotient X).terminalFrontier U) ⊆
      G.roof ((G.quotient X).terminalFrontier W) := by
  let S := (G.quotient X).terminalFrontier W
  have hEss : G.essential X ⊆ G.roof S := by
    simpa only [S] using
      G.essential_subset_original_roof_of_quotient_wave_general hNoEnter hW
  have hRoofX : G.roof X ⊆ G.roof S := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  intro v hv
  by_cases hvStrict : v ∈ G.strictRoof X
  · exact hRoofX hvStrict.1
  · have hvQ : v ∈ (G.quotient X).roof
        ((G.quotient X).terminalFrontier U) := by
      apply (G.quotient X).roof_mono Set.sdiff_subset
      exact G.roof_sdiff_strictRoof_subset_quotient_roof X
        ((G.quotient X).terminalFrontier U) ⟨hv, hvStrict⟩
    exact G.quotient_roof_subset_original_roof_of_essential X S hEss
      ⟨hUW hvQ, hvStrict⟩

/-- If the new essential frontier avoids the old strict roof, ambient roof
preservation upgrades to ambient strict-roof preservation.  The explicit
disjointness hypothesis is necessary in this general form. -/
theorem strictRoof_terminalFrontier_mono_of_roof_mono_of_disjoint
    {S T : Set V} (hRoof : G.roof S ⊆ G.roof T)
    (hDisjoint : Disjoint (G.essential T) (G.strictRoof S)) :
    G.strictRoof S ⊆ G.strictRoof T := by
  intro v hv
  exact ⟨hRoof hv.1, fun hvEss ↦
    Set.disjoint_left.1 hDisjoint hvEss hv⟩

/-- The essential frontier of an arrow avoids the strict roof of its left
input.  This is the concrete content of source Lemma 3.18. -/
theorem essential_terminalFrontier_arrow_disjoint_strictRoof_left
    {U W : Set G.DPath} (hU : G.IsWave U) (hW : G.IsWave W) :
    Disjoint (G.essential (G.terminalFrontier (G.arrow U W)))
      (G.strictRoof (G.terminalFrontier U)) := by
  rw [G.essential_terminalFrontier_arrow_eq_union hU hW]
  apply Set.disjoint_left.2
  intro z hzEss hzStrict
  by_cases hzU : z ∈ G.terminalFrontier U
  · have hzRoofWithout : z ∈
        G.roof (G.terminalFrontier U \ {z}) := by
      by_contra h
      exact hzStrict.2 ⟨hzU, h⟩
    apply hzEss.2
    apply G.roof_mono _ hzRoofWithout
    intro x hx
    exact ⟨Or.inl hx.1, hx.2⟩
  · apply hzEss.2
    apply G.roof_mono _ hzStrict.1
    intro x hx
    exact ⟨Or.inl hx, fun hxz ↦ hzU (hxz ▸ hx)⟩

/-- Arrowing on the right preserves the strict roof of the left wave.
This is the strict-roof form of Lemmas 3.17--3.18. -/
theorem strictRoof_terminalFrontier_subset_arrow_left
    {U W : Set G.DPath} (hU : G.IsWave U) (hW : G.IsWave W) :
    G.strictRoof (G.terminalFrontier U) ⊆
      G.strictRoof (G.terminalFrontier (G.arrow U W)) := by
  apply G.strictRoof_terminalFrontier_mono_of_roof_mono_of_disjoint
  · exact G.roofLE_of_forwardExtension (G.isWave_arrow hU hW)
      (G.forwardExtension_arrow U W)
  · exact G.essential_terminalFrontier_arrow_disjoint_strictRoof_left hU hW

/-- Transport to a larger quotient followed by a right arrow preserves the
old original-web roof. -/
theorem roof_terminalFrontier_subset_arrow_waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (U : (G.quotient X).Wave) (W : (G.quotient Y).Wave) :
    G.roof ((G.quotient X).terminalFrontier U.1) ⊆
      G.roof ((G.quotient Y).terminalFrontier
        ((G.quotient Y).arrow
          (G.waveToLargerQuotient hNoEnter hXY U).1 W.1)) := by
  let T := G.waveToLargerQuotient hNoEnter hXY U
  have hArrow : (G.quotient Y).IsWave
      ((G.quotient Y).arrow T.1 W.1) :=
    (G.quotient Y).isWave_arrow T.2 W.2
  have hLE : (G.quotient Y).RoofLE T.1
      ((G.quotient Y).arrow T.1 W.1) :=
    (G.quotient Y).roofLE_of_forwardExtension hArrow
      ((G.quotient Y).forwardExtension_arrow T.1 W.1)
  exact (G.roof_terminalFrontier_subset_waveToLargerQuotient
    hNoEnter hXY U).trans
      (G.original_roofLE_of_quotient_roofLE hNoEnter hArrow hLE)

/-- The old original-web strict roof survives transport followed by an
arrow whenever the new ambient essential frontier avoids that old strict
roof.  This states the exact extra condition needed beyond roof
preservation. -/
theorem strictRoof_terminalFrontier_subset_arrow_waveToLargerQuotient_of_disjoint
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (U : (G.quotient X).Wave) (W : (G.quotient Y).Wave)
    (hDisjoint : Disjoint
      (G.essential ((G.quotient Y).terminalFrontier
        ((G.quotient Y).arrow
          (G.waveToLargerQuotient hNoEnter hXY U).1 W.1)))
      (G.strictRoof ((G.quotient X).terminalFrontier U.1))) :
    G.strictRoof ((G.quotient X).terminalFrontier U.1) ⊆
      G.strictRoof ((G.quotient Y).terminalFrontier
        ((G.quotient Y).arrow
          (G.waveToLargerQuotient hNoEnter hXY U).1 W.1)) := by
  exact G.strictRoof_terminalFrontier_mono_of_roof_mono_of_disjoint
    (G.roof_terminalFrontier_subset_arrow_waveToLargerQuotient
      hNoEnter hXY U W) hDisjoint

/-! ## The raw-union quotient -/

/-- Each stage wave retains its original-web terminal roof after transport
to the quotient by the raw union. -/
theorem roof_terminalFrontier_subset_commonQuotientStage
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) (i : ℕ) :
    G.roof ((G.quotient (X i)).terminalFrontier (W i).1) ⊆
      G.roof ((G.quotient (commonQuotientSet X)).terminalFrontier
        (G.commonQuotientStage hNoEnter X W i).1) :=
  G.roof_terminalFrontier_subset_waveToLargerQuotient hNoEnter
    (subset_commonQuotientSet X i) (W i)

/-- Every stage's terminal roof, interpreted in the original web, is
contained in the terminal roof of the countable up-arrow in the raw-union
quotient. -/
theorem roof_terminalFrontier_subset_commonQuotientOmegaArrow
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) (i : ℕ) :
    G.roof ((G.quotient (X i)).terminalFrontier (W i).1) ⊆
      G.roof ((G.quotient (commonQuotientSet X)).terminalFrontier
        (G.commonQuotientOmegaArrow hNoEnter X W).1) := by
  have hStage := G.roof_terminalFrontier_subset_commonQuotientStage
    hNoEnter X W i
  have hFinal := G.original_roofLE_of_quotient_roofLE
    (X := commonQuotientSet X) hNoEnter
    (G.commonQuotientOmegaArrow hNoEnter X W).2
    (G.roofLE_commonQuotientOmegaArrow hNoEnter X W i)
  exact hStage.trans hFinal

/-- Pointwise stage-zero form used by the Section 6 recursion. -/
theorem mem_roof_commonQuotientOmegaArrow_of_mem_stage_zero
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) {y : V}
    (hy : y ∈ G.roof
      ((G.quotient (X 0)).terminalFrontier (W 0).1)) :
    y ∈ G.roof ((G.quotient (commonQuotientSet X)).terminalFrontier
      (G.commonQuotientOmegaArrow hNoEnter X W).1) :=
  G.roof_terminalFrontier_subset_commonQuotientOmegaArrow
    hNoEnter X W 0 hy

/-- Stage-zero strict-roof input implies the roof conclusion used at the
end of the raw-union construction. -/
theorem mem_roof_commonQuotientOmegaArrow_of_mem_strictRoof_stage_zero
    (hNoEnter : G.NoEdgeEnters G.source) (X : ℕ → Set V)
    (W : ∀ i, (G.quotient (X i)).Wave) {y : V}
    (hy : y ∈ G.strictRoof
      ((G.quotient (X 0)).terminalFrontier (W 0).1)) :
    y ∈ G.roof ((G.quotient (commonQuotientSet X)).terminalFrontier
      (G.commonQuotientOmegaArrow hNoEnter X W).1) :=
  G.mem_roof_commonQuotientOmegaArrow_of_mem_stage_zero
    hNoEnter X W ((G.strictRoof_subset_roof _) hy)

end DWeb
end Erdos599
