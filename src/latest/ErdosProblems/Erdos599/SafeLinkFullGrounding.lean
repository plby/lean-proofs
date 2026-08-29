/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkFullClosure

/-!
# Grounding for the full Section 6 closure

The full quotient transport preserves every source-rooted component.  This
file records the corresponding ambient-roof transport and uses it to prove
Proposition 6.3(c) for the full dependent closure.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Passing a wave to its full quotient component wave preserves its old
ambient terminal roof. -/
theorem roof_terminalFrontier_subset_fullQuotientWave
    (hNoEnter : G.NoEdgeEnters G.source) (X : Set V) (W : G.Wave) :
    G.roof (G.terminalFrontier W.1) ⊆
      G.roof ((G.quotient X).terminalFrontier
        (G.fullQuotientWave hNoEnter X W).1) := by
  let Q := G.fullQuotientWave hNoEnter X W
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
            (G.terminalFrontier W.1) ⟨hv, hvStrict⟩)
      · intro z hz
        exact G.terminalFrontiers_subset_fullQuotientWave
          hNoEnter X W (Or.inl hz)
    exact G.quotientWave_roof_subset_original_roof_general
      hNoEnter Q.2 hvQ

/-- Moving a quotient wave by the full transport from `G / X` to `G / Y`
preserves its terminal roof when both frontiers are read in `G`. -/
theorem roof_terminalFrontier_subset_fullWaveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    G.roof ((G.quotient X).terminalFrontier W.1) ⊆
      G.roof ((G.quotient Y).terminalFrontier
        (G.fullWaveToLargerQuotient hNoEnter hXY W).1) := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    H.fullQuotientWave hNoEnter.quotient Y W
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  let Q := G.fullWaveToLargerQuotient hNoEnter hXY W
  let S := (G.quotient Y).terminalFrontier Q.1
  have hQZ : Q = heq ▸ Z := by
    apply Subtype.ext
    rfl
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
        ((G.quotient X).terminalFrontier W.1 \ G.strictRoof X) := by
      simpa only [H] using
        (G.roof_sdiff_strictRoof_subset_quotient_roof X
          ((G.quotient X).terminalFrontier W.1) ⟨hv, hvStrict⟩)
    have hvH : v ∈ H.roof ((G.quotient X).terminalFrontier W.1) :=
      H.roof_mono Set.sdiff_subset hvH0
    have hvZ : v ∈ H.roof ((H.quotient Y).terminalFrontier Z.1) :=
      H.roof_terminalFrontier_subset_fullQuotientWave
        hNoEnter.quotient Y W hvH
    have hvQ : v ∈ (G.quotient X).roof S := by
      change v ∈ (G.quotient X).roof
        ((G.quotient Y).terminalFrontier Q.1)
      rw [hQZ]
      rw [terminalFrontier_castWebWave heq Z]
      exact hvZ
    exact G.quotient_roof_subset_original_roof_of_essential X S hEssX
      ⟨hvQ, hvStrict⟩

end DWeb

namespace SafeLink

variable {V : Type u}

/-- Proposition 6.3(c) for the full dependent Section 6 closure. -/
theorem sectionSixFullAccumClosure_grounding
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T : Set V} (hT : Maximal (G.IsTreeSet a) T) :
    let base := G.delete {a}
    let hNoEnter : base.NoEdgeEnters base.source :=
      delete_root_noEdgeEnters_source G hG a
    let F := fun z ↦ boundaryObstruction G hG hT z
    let K := groundingSet G a T
    let Y := G.outerBoundary T
    let Q := nonBoundedTreeVertices G a T
    let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T
    let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T
    ∀ y t, t ∈ X y \ Q →
      K t ⊆ X y ∧
      t ∈ G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a (X y) (M y).1)) := by
  dsimp only
  intro y t ht
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
  obtain ⟨n, htn⟩ := Set.mem_iUnion.mp ht.1
  have htStage : t ∈
      (base.sectionSixFullAccumStage hNoEnter F K Y Q T y n).carrier \ Q :=
    ⟨htn, ht.2⟩
  have hKsucc : K t ⊆
      (base.sectionSixFullAccumStage
        hNoEnter F K Y Q T y (n + 1)).carrier :=
    base.sectionSixFullAccum_K_subset_succ
      hNoEnter F K Y Q T y n htStage
  have hKX : K t ⊆ X := hKsucc.trans
    (base.sectionSixFullAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y (n + 1))
  refine ⟨by simpa only [K, X] using hKX, ?_⟩

  have htOffRoot : t ∈ T \ {a} := by
    apply G.sectionSixFullAccumStage_carrier_subset_offRoot a hNoEnter
      F K Y Q T y
      (boundaryObstruction_subset G hG hT)
      (groundingSet_subset_offRoot G a T) n
    exact htn
  have htBounded : IsBoundedTreeVertex G a T t := by
    by_contra htNotBounded
    exact ht.2 ⟨htOffRoot.1, htNotBounded⟩
  obtain ⟨U, hU, htStrictG⟩ :=
    exists_wave_for_groundingSet G a T htBounded
  let Uw : (base.quotient (K t)).Wave := ⟨U, hU⟩
  let s := base.sectionSixFullAccumStage hNoEnter F K Y Q T y n
  let Xnext := base.sectionSixAccumNextCarrier F K Y Q T s
  have hKnext : K t ⊆ Xnext := by
    intro x hx
    exact Or.inl (Or.inr
      (Set.mem_iUnion_of_mem t (Set.mem_iUnion_of_mem htStage hx)))
  let oldAtNext := base.fullWaveToLargerQuotient hNoEnter hKnext Uw
  let next := base.sectionSixFullAccumNext hNoEnter F K Y Q T s

  have hRoofTransport :
      base.roof ((base.quotient (K t)).terminalFrontier Uw.1) ⊆
        base.roof ((base.quotient Xnext).terminalFrontier oldAtNext.1) :=
    base.roof_terminalFrontier_subset_fullWaveToLargerQuotient
      hNoEnter hKnext Uw

  have hOldNextQ :
      (base.quotient Xnext).RoofLE oldAtNext.1 next.wave.1 := by
    exact base.sectionSixFullAccumNext_roofs_every_wave
      hNoEnter F K Y Q T s oldAtNext
  have hRoofNext :
      base.roof ((base.quotient Xnext).terminalFrontier oldAtNext.1) ⊆
        base.roof ((base.quotient Xnext).terminalFrontier next.wave.1) :=
    base.original_roofLE_of_quotient_roofLE hNoEnter
      next.wave.2 hOldNextQ

  have hXnextX : Xnext ⊆ X := by
    intro x hx
    apply Set.mem_iUnion_of_mem (n + 1)
    change x ∈ Xnext
    exact hx
  let commonNext := base.fullWaveToLargerQuotient hNoEnter hXnextX next.wave

  have hRoofCommonStage :
      base.roof ((base.quotient Xnext).terminalFrontier next.wave.1) ⊆
        base.roof ((base.quotient X).terminalFrontier commonNext.1) := by
    exact base.roof_terminalFrontier_subset_fullWaveToLargerQuotient
      hNoEnter hXnextX next.wave

  have hCommonNextEq : commonNext =
      base.sectionSixFullAccumCommonStage
        hNoEnter F K Y Q T y (n + 1) := by
    apply Subtype.ext
    rfl

  have hCommonFinalQ :
      (base.quotient X).RoofLE commonNext.1 M.1 := by
    rw [hCommonNextEq]
    exact base.sectionSixFullAccumCommonStage_roofLE
      hNoEnter F K Y Q T y (n + 1)
  have hRoofFinal :
      base.roof ((base.quotient X).terminalFrontier commonNext.1) ⊆
        base.roof ((base.quotient X).terminalFrontier M.1) :=
    base.original_roofLE_of_quotient_roofLE hNoEnter M.2 hCommonFinalQ

  have hRoofAll :
      base.roof ((base.quotient (K t)).terminalFrontier U) ⊆
        base.roof ((base.quotient X).terminalFrontier M.1) :=
    hRoofTransport.trans
      (hRoofNext.trans (hRoofCommonStage.trans hRoofFinal))
  have htStrictBaseOld :
      t ∈ base.strictRoof ((base.quotient (K t)).terminalFrontier U) := by
    have hdelete := G.strictRoof_subset_delete_strictRoof
      ((base.quotient (K t)).terminalFrontier U) ({a} : Set V)
    apply hdelete
    change t ∈ G.strictRoof
      ((base.quotient (K t)).terminalFrontier U)
    rw [← base.terminalFrontier_liftQuotientFamily]
    rw [← G.terminalFrontier_liftDeleteFamily]
    exact htStrictG
  have htStrictBaseFinal :
      t ∈ base.strictRoof ((base.quotient X).terminalFrontier M.1) :=
    base.strictRoof_mono_of_roof_mono hRoofAll htStrictBaseOld
  have htNeA : t ≠ a := by
    intro hta
    exact htOffRoot.2 (hta ▸ Set.mem_singleton a)
  have htStrictFinal := strictRoof_delete_source_subset_ambient_of_ne
    G hG ha htNeA htStrictBaseFinal
  change t ∈ G.strictRoof (G.terminalFrontier
    (G.liftDeleteFamily {a} (base.liftQuotientFamily X M.1)))
  rw [G.terminalFrontier_liftDeleteFamily,
    base.terminalFrontier_liftQuotientFamily]
  exact htStrictFinal

end SafeLink

end Erdos599
