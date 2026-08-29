/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularContinuation
import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.QuotientRoofTransport
import ErdosProblems.Erdos599.SliceSpliceSource
import ErdosProblems.Erdos599.LadderFrontierInvariants

/-!
# Re-entering the ambient web after a singular quotient step

The inner recursion in Assertion 9.17 applies the lower-cardinal half-way
theorem in the quotient by the current stop-over.  This file records the
non-circular part of the re-entry argument.  A weak stop-over in that
quotient is enlarged to the source of its own quotient.  The enlargement
separates the whole quotient source, contains the old stop-over, retains the
height witness, and has unhindered quotient.  Since quotients preserve the
no-incoming-source property, this construction can be iterated even though a
quotient need not be normalized in the stronger edge-by-edge sense.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularQuotientReentry

universe u

variable {V : Type u}

/-- A trimmed set is contained in the source of its quotient whenever no
edge enters the old source. -/
theorem trimmed_subset_quotient_source
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source) {C : Set V}
    (hC : IsTrimmedSeparator G C) :
    C ⊆ (G.quotient C).source := by
  rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
    hNoEnter]
  intro x hxC
  refine ⟨Or.inr hxC, ?_⟩
  rintro ⟨_hxRoof, hxNotEssential⟩
  apply hxNotEssential
  rw [hC]
  exact hxC

/-- The terminal frontier of a quotient wave roofs the old source.  This is
the no-incoming-source form of the height-witness transport used in the
canonical enlargement. -/
theorem source_subset_roof_quotientWave_terminal
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    (hX : X ⊆ G.sourceᶜ) {U : Set (G.quotient X).DPath}
    (hU : (G.quotient X).IsWave U) :
    G.source ⊆ G.roof ((G.quotient X).terminalFrontier U) := by
  have hSourceX : Disjoint G.source X := by
    rw [Set.disjoint_left]
    intro x hxSource hxX
    exact hX hxX hxSource
  let S := (G.quotient X).terminalFrontier U
  have hEss : G.essential X ⊆ G.roof S := by
    simpa only [S] using
      G.essential_subset_original_roof_of_quotient_wave
        hNoEnter hSourceX hU
  have hRoofX : G.roof X ⊆ G.roof S := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  intro a ha
  by_cases haStrict : a ∈ G.strictRoof X
  · exact hRoofX haStrict.1
  · have haQSource : a ∈ (G.quotient X).source := by
      rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters
        hNoEnter hSourceX]
      exact ⟨Or.inl ha, haStrict⟩
    have haQRoof : a ∈ (G.quotient X).roof S := hU.2.2 haQSource
    exact G.quotient_roof_subset_original_roof_of_essential X S hEss
      ⟨haQRoof, haStrict⟩

/-- Quotienting an unhindered web by its complete source preserves
unhinderedness. -/
theorem quotient_source_isUnhindered
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
    (hG : G.IsUnhindered) :
    (G.quotient G.source).IsUnhindered := by
  rw [(G.quotient G.source).isUnhindered_iff]
  intro U hU
  have hessential : G.essential G.source = G.source := by
    apply Set.Subset.antisymm (G.essential_subset G.source)
    intro a ha
    have htrimWave : G.IsWave (G.essentialWarpPart G.trivialWave) :=
      G.isWave_trivialWave.essentialWarpPart
    have hinitial :
        G.initialSet (G.essentialWarpPart G.trivialWave) = G.source :=
      G.isUnhindered_iff.mp hG _ htrimWave
    have haInitial : a ∈ G.initialSet (G.essentialWarpPart G.trivialWave) :=
      hinitial.symm ▸ ha
    obtain ⟨p, hp, hpstart⟩ := haInitial
    rcases hp with ⟨⟨b, hb, rfl⟩, t, hpterm, ht⟩
    have hba : b = a := by simpa using hpstart
    have hta : t = a := by
      have : some b = some t := (G.terminal?_trivialPath b).trans hpterm
      exact (Option.some.inj this).symm.trans hba
    simpa only [G.terminalFrontier_trivialWave, hta] using ht
  have hqsource : (G.quotient G.source).source = G.source := by
    rw [DWeb.quotient_source, Set.union_self, hessential]
  let L : Set G.DPath := G.liftQuotientFamily G.source U
  have hLwave : G.IsWave L := by
    refine ⟨DWeb.IsWarp.liftQuotientFamily G hU.1, ?_, ?_⟩
    · dsimp only [L]
      rw [G.initialSet_liftQuotientFamily]
      simpa only [hqsource] using hU.2.1
    · dsimp only [L]
      rw [G.terminalFrontier_liftQuotientFamily]
      intro a ha
      apply G.quotientWave_roof_subset_original_roof_general hNoEnter hU
      apply hU.2.2
      simpa only [hqsource] using ha
  have hLinitial : G.initialSet L = G.source :=
    G.isUnhindered_iff.mp hG L hLwave
  dsimp only [L] at hLinitial
  rw [G.initialSet_liftQuotientFamily] at hLinitial
  exact hLinitial.trans hqsource.symm

/-- Canonically enlarge a weak half-way stop-over under the exact invariant
available in every iterated quotient: no edge enters the current source. -/
theorem exists_separatingStopover_of_stopover
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set G.DPath} {C : Set V}
    (hstop : IsHalfwayStopover G W C) {kappa : Cardinal.{u}}
    (hheight : HeightAtMost G C kappa) :
    ∃ D : Set V,
      IsSeparatingHalfwayStopover G W D ∧ HeightAtMost G D kappa ∧
      D ⊆ G.source ∪ C := by
  let D : Set V := (G.quotient C).source
  have hCD : C ⊆ D :=
    trimmed_subset_quotient_source G hNoEnter hstop.minimal
  have hDsub : D ⊆ G.source ∪ C := by
    intro x hx
    exact G.essential_subset (G.source ∪ C) hx
  have hsep : IsSeparatorFrom G G.source D := by
    intro a ha
    change a ∈ G.roof (G.essential (G.source ∪ C))
    rw [G.roof_essential]
    exact G.subset_roof (G.source ∪ C) (Or.inl ha)
  have htrim : IsTrimmedSeparator G D := by
    change G.essential (G.essential (G.source ∪ C)) =
      G.essential (G.source ∪ C)
    exact G.essential_idem (G.source ∪ C)
  have hlinkage : IsLinkageBetween G G.source D W := by
    refine ⟨hstop.linkage.isWarp, hstop.linkage.finiteCharacter,
      hstop.linkage.initialSet_eq, hstop.linkage.terminalFrontier_subset.trans hCD,
      ?_⟩
    intro p hp
    obtain ⟨q, rfl, hends, hsource⟩ := hstop.linkage.endpointPure p hp
    refine ⟨q, rfl, ?_, hsource⟩
    have hunion : G.source ∪ D = G.source ∪ C := by
      apply Set.Subset.antisymm
      · exact Set.union_subset Set.subset_union_left
          (hDsub.trans (Set.union_subset Set.subset_union_left
            Set.subset_union_right))
      · exact Set.union_subset Set.subset_union_left
          (hCD.trans Set.subset_union_right)
    simpa only [hunion] using hends
  have hquotient : (G.quotient D).IsUnhindered := by
    have hiter := quotient_source_isUnhindered
      (G.quotient C) (DWeb.NoEdgeEnters.quotient G hNoEnter)
        hstop.quotient_unhindered
    have heq : (G.quotient C).quotient D = G.quotient D := by
      calc
        (G.quotient C).quotient D = G.quotient (C ∪ D) :=
          G.quotient_quotient_eq_union C D hNoEnter
        _ = G.quotient D := by rw [Set.union_eq_right.2 hCD]
    rwa [heq] at hiter
  have hheightD : HeightAtMost G D kappa := by
    obtain ⟨X, ⟨hX, U, hU, hCU⟩, hXcard⟩ := hheight
    refine ⟨X, ⟨hX, U, hU, ?_⟩, hXcard⟩
    have hsourceRoof := source_subset_roof_quotientWave_terminal
      G hNoEnter hX hU
    exact hDsub.trans (Set.union_subset hsourceRoof hCU)
  exact ⟨D, ⟨⟨⟨hlinkage, htrim, hquotient⟩, hsep⟩, hheightD, hDsub⟩⟩

/-- The quotient-level form used by the singular successor construction.
The canonical enlargement lies in the union of the quotient source and the
original weak stop-over.  Consequently adjoining the old ambient stop-over
to it does not introduce any vertices beyond the two genuine endpoint
sets. -/
theorem exists_quotientSeparatingStopover
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {D : Set V} {U : Set (G.quotient D).DPath} {C : Set V}
    (hstop : IsHalfwayStopover (G.quotient D) U C)
    {kappa : Cardinal.{u}}
    (hheight : HeightAtMost (G.quotient D) C kappa) :
    ∃ E : Set V,
      IsSeparatingHalfwayStopover (G.quotient D) U E ∧
      HeightAtMost (G.quotient D) E kappa ∧
      E ⊆ (G.quotient D).source ∪ C ∧
      (G.quotient (D ∪ E)).IsUnhindered := by
  obtain ⟨E, hE, hheightE, hEsub⟩ :=
    exists_separatingStopover_of_stopover
      (DWeb.NoEdgeEnters.quotient G hNoEnter) hstop hheight
  have heq : (G.quotient D).quotient E = G.quotient (D ∪ E) :=
    G.quotient_quotient_eq_union D E hNoEnter
  refine ⟨E, hE, hheightE, hEsub, ?_⟩
  rw [← heq]
  exact hE.quotient_unhindered

/-! ## Uncrossing the nested separator -/

/-- If `D` is a trimmed ambient separator and `E` separates the source of
`G / D`, then every old stop-over vertex is roofed by `E` in the ambient
web.  The proof passes the suffix after the last visit to `D` through the
quotient. -/
theorem oldStopover_subset_roof_new
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hE : IsSeparatorFrom (G.quotient D) (G.quotient D).source E) :
    D ⊆ G.roof E := by
  intro d hd p hp
  have hmeetD : G.Meets p D :=
    ⟨p.start, p.start_mem_support, hp.1 ▸ hd⟩
  let hm : p.walk.Meets D :=
    ⟨hmeetD.choose, hmeetD.choose_spec.1, hmeetD.choose_spec.2⟩
  let L := p.walk.lastHit D hm
  have hLEss : L.startpoint ∈ G.essential D :=
    G.lastHit_mem_essential D p hp hmeetD
  have hLSource : L.startpoint ∈ (G.quotient D).source := by
    rw [hD.quotient_source_eq]
    exact (Set.ext_iff.mp hD.stopover.minimal L.startpoint).mp hLEss
  obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
    G.exists_quotientPath_from_lastHit D p hp hmeetD
  have hqTarget : (G.quotient D).IsTargetPathFrom L.startpoint q :=
    ⟨hqStart, hqFinish ▸ hp.2⟩
  obtain ⟨e, heq, heE⟩ := hE hLSource q hqTarget
  have heL : e ∈ L.walk.support := by
    rw [hqSupport] at heq
    exact heq
  exact ⟨e, L.support_subset heL, heE⟩

/-- The new quotient separator also separates the original ambient source. -/
theorem newStopover_isSeparator
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hE : IsSeparatorFrom (G.quotient D) (G.quotient D).source E) :
    IsSeparatorFrom G G.source E := by
  exact hD.separator.trans
    (G.roof_cut (oldStopover_subset_roof_new hD hE))

/-- Adding the old stop-over to the new nested separator changes neither
its ambient roof nor its ambient essential frontier. -/
theorem roof_union_old_new_eq_new
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hE : IsSeparatorFrom (G.quotient D) (G.quotient D).source E) :
    G.roof (D ∪ E) = G.roof E := by
  apply Set.Subset.antisymm
  · apply G.roof_cut
    exact Set.union_subset (oldStopover_subset_roof_new hD hE)
      (G.subset_roof E)
  · exact G.roof_mono Set.subset_union_right

theorem essential_union_old_new_eq_new
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hE : IsSeparatorFrom (G.quotient D) (G.quotient D).source E) :
    G.essential (D ∪ E) = G.essential E := by
  rw [Set.union_comm]
  exact RelationalRoof.essential_union_eq_of_subset_roof
    G.graph.Adj G.target (oldStopover_subset_roof_new hD hE)

/-- Trimmedness in the nested quotient uncrosses to trimmedness of the new
stop-over in the ambient web. -/
theorem newStopover_isTrimmed
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    IsTrimmedSeparator G E := by
  have heq : (G.quotient D).quotient E = G.quotient (D ∪ E) :=
    G.quotient_quotient_eq_union D E hNoEnter
  have hsourceUnion : (G.quotient (D ∪ E)).source = E := by
    rw [← heq]
    exact hE.quotient_source_eq
  change G.essential (G.source ∪ (D ∪ E)) = E at hsourceUnion
  have hroof : G.source ∪ D ⊆ G.roof E :=
    Set.union_subset (newStopover_isSeparator hD hE.separator)
      (oldStopover_subset_roof_new hD hE.separator)
  have hessential : G.essential (G.source ∪ (D ∪ E)) = G.essential E := by
    calc
      G.essential (G.source ∪ (D ∪ E)) =
          G.essential (E ∪ (G.source ∪ D)) := by
            congr 1
            ext x
            simp only [Set.mem_union]
            tauto
      _ = G.essential E :=
        RelationalRoof.essential_union_eq_of_subset_roof
          G.graph.Adj G.target hroof
  exact hessential.symm.trans hsourceUnion

/-- Quotienting by the new uncrossed stop-over is literally the same web
as first quotienting by the old stop-over and then by the new one. -/
theorem quotient_new_eq_iterated
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    G.quotient E = (G.quotient D).quotient E := by
  have hNested : (G.quotient D).quotient E = G.quotient (D ∪ E) :=
    G.quotient_quotient_eq_union D E hNoEnter
  have hRoof : G.roof E = G.roof (D ∪ E) :=
    (roof_union_old_new_eq_new hD hE.separator).symm
  have hEssential : G.essential E = G.essential (D ∪ E) :=
    (essential_union_old_new_eq_new hD hE.separator).symm
  have hTrimE : G.essential E = E :=
    newStopover_isTrimmed hNoEnter hD hE
  have hStrict : G.strictRoof E = G.strictRoof (D ∪ E) := by
    rw [DWeb.strictRoof, DWeb.strictRoof, hRoof, hEssential]
  have hOldDiffStrict : D \ E ⊆ G.strictRoof (D ∪ E) := by
    intro x hx
    refine ⟨G.subset_roof (D ∪ E) (Or.inl hx.1), ?_⟩
    intro hxEss
    have hxEssE := (Set.ext_iff.mp hEssential x).mpr hxEss
    exact hx.2 ((Set.ext_iff.mp hTrimE x).mp hxEssE)
  have hSourceE : (G.quotient E).source = E :=
    SingularContinuation.quotient_source_eq_stopover G
      (newStopover_isSeparator hD hE.separator)
      (newStopover_isTrimmed hNoEnter hD hE)
  have hSourceUnion : (G.quotient (D ∪ E)).source = E := by
    rw [← hNested]
    exact hE.quotient_source_eq
  rw [hNested]
  rw [DWeb.mk.injEq]
  refine ⟨?_, hSourceE.trans hSourceUnion.symm, rfl⟩
  ext a b
  change
    (G.graph.Adj a b ∧ a ∉ G.strictRoof E ∧
        b ∉ G.strictRoof E ∧ b ∉ E) ↔
      (G.graph.Adj a b ∧ a ∉ G.strictRoof (D ∪ E) ∧
        b ∉ G.strictRoof (D ∪ E) ∧ b ∉ D ∪ E)
  rw [hStrict]
  constructor
  · rintro ⟨hab, ha, hb, hbE⟩
    refine ⟨hab, ha, hb, ?_⟩
    rintro (hbD | hbE')
    · exact hb (hOldDiffStrict ⟨hbD, hbE⟩)
    · exact hbE hbE'
  · rintro ⟨hab, ha, hb, hbUnion⟩
    exact ⟨hab, ha, hb, fun hbE ↦ hbUnion (Or.inr hbE)⟩

/-- The new stop-over has unhindered ambient quotient. -/
theorem quotient_new_isUnhindered
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    (G.quotient E).IsUnhindered := by
  rw [quotient_new_eq_iterated hNoEnter hD hE]
  exact hE.quotient_unhindered

/-! ## The future-safe frozen/restricted splice -/

/-- Old members whose terminal already lies in the new stop-over. -/
def frozenAt (G : DWeb V) (W : Set G.DPath) (E : Set V) : Set G.DPath :=
  {p | p ∈ W ∧ ∃ e ∈ E, G.terminal? p = some e}

/-- Old members which must genuinely be continued past the old stop-over. -/
def pendingAt (G : DWeb V) (W : Set G.DPath) (E : Set V) : Set G.DPath :=
  W \ frozenAt G W E

theorem frozenAt_union_pendingAt (G : DWeb V) (W : Set G.DPath)
    (E : Set V) :
    frozenAt G W E ∪ pendingAt G W E = W := by
  ext p
  simp only [frozenAt, pendingAt, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_sdiff]
  tauto

/-- Only quotient paths starting outside the new stop-over are used to
continue pending old members.  Quotient paths starting in `E` correspond
to old members frozen at this step. -/
def quotientPending (G : DWeb V) (D E : Set V)
    (U : Set (G.quotient D).DPath) : Set (G.quotient D).DPath :=
  (G.quotient D).startPaths U Eᶜ

theorem quotientPending_subset (G : DWeb V) (D E : Set V)
    (U : Set (G.quotient D).DPath) :
    quotientPending G D E U ⊆ U :=
  fun _ hp ↦ hp.1

theorem quotientPending_initial_not_mem
    (G : DWeb V) (D E : Set V) (U : Set (G.quotient D).DPath)
    {p : (G.quotient D).DPath} (hp : p ∈ quotientPending G D E U) :
    p.initial ∉ E :=
  hp.2

/-- The new uncrossed stop-over avoids the old strict roof. -/
theorem disjoint_newStopover_strictRoof_old
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    Disjoint E (G.strictRoof D) := by
  have hdis := G.disjoint_essential_union_strictRoof_left D E
  rw [essential_union_old_new_eq_new hD hE.separator,
    newStopover_isTrimmed hNoEnter hD hE] at hdis
  exact hdis

/-- Every old member which is frozen at `E` meets `E` only at its
terminal. -/
theorem frozenAt_terminalClean
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : SingularContinuation.TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    SingularContinuation.TerminalCleanAt G (frozenAt G W E) E := by
  have hroof : G.vertexSet W ⊆ G.roof D :=
    SingularContinuation.linkage_vertexSet_subset_roof
      G hD.linkage hD.separator hclean
  have hdis := disjoint_newStopover_strictRoof_old hNoEnter hD hE
  intro p hp x hxp hxE
  have hxRoof : x ∈ G.roof D := hroof ⟨p, hp.1, hxp⟩
  have hxNotStrict : x ∉ G.strictRoof D := by
    intro hxStrict
    exact Set.disjoint_left.1 hdis hxE hxStrict
  have hxEssential : x ∈ G.essential D := by
    by_contra hxNotEssential
    exact hxNotStrict ⟨hxRoof, hxNotEssential⟩
  have hxD : x ∈ D :=
    (Set.ext_iff.mp hD.stopover.minimal x).mp hxEssential
  exact hclean p hp.1 x hxp hxD

/-- A pending old member has no contact at all with the new stop-over. -/
theorem pendingAt_disjoint_newStopover
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : SingularContinuation.TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    Disjoint (G.vertexSet (pendingAt G W E)) E := by
  have hroof : G.vertexSet W ⊆ G.roof D :=
    SingularContinuation.linkage_vertexSet_subset_roof
      G hD.linkage hD.separator hclean
  have hdis := disjoint_newStopover_strictRoof_old hNoEnter hD hE
  apply Set.disjoint_left.2
  intro x hxPending hxE
  obtain ⟨p, hp, hxp⟩ := hxPending
  have hxRoof : x ∈ G.roof D := hroof ⟨p, hp.1, hxp⟩
  have hxNotStrict : x ∉ G.strictRoof D := by
    intro hxStrict
    exact Set.disjoint_left.1 hdis hxE hxStrict
  have hxEssential : x ∈ G.essential D := by
    by_contra hxNotEssential
    exact hxNotStrict ⟨hxRoof, hxNotEssential⟩
  have hxD : x ∈ D :=
    (Set.ext_iff.mp hD.stopover.minimal x).mp hxEssential
  have hterminal := hclean p hp.1 x hxp hxD
  exact hp.2 ⟨hp.1, x, hxE, hterminal⟩

/-- The restricted quotient continuation meets the new stop-over only at
its terminal. -/
theorem lifted_quotientPending_terminalClean
    {G : DWeb V} {D E : Set V} {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    SingularContinuation.TerminalCleanAt G
      (SingularContinuation.liftedQuotientFamily G D
        (quotientPending G D E U)) E := by
  intro p hp x hxp hxE
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨f, hf, hends, _hsource⟩ :=
    hE.linkage.endpointPure q hq.1
  subst q
  rw [G.support_liftQuotientPath] at hxp
  change x ∈ f.support at hxp
  have hxEnds : x ∈ ({f.start, f.finish} : Set V) := by
    rw [← hends]
    exact ⟨hxp, Or.inr hxE⟩
  rcases Set.mem_insert_iff.1 hxEnds with hxStart | hxFinish
  · subst x
    exact False.elim (hq.2 hxE)
  · change some f.finish = some x
    exact congrArg some (Set.mem_singleton_iff.1 hxFinish).symm

/-- Concrete name for the frozen/restricted splice, used when subsequent
properties (notably target links) must refer to the actual constructed
family. -/
noncomputable def frozenRestrictedContinuation
    (G : DWeb V) {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : SingularContinuation.TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    Set G.DPath := by
  let P := pendingAt G W E
  let R := quotientPending G D E U
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    SingularContinuation.linkage_vertexSet_subset_roof
      G hD.linkage hD.separator hclean
  have hProof : G.vertexSet P ⊆ G.roof D := by
    rintro x ⟨p, hp, hxp⟩
    exact hWroof ⟨p, hp.1, hxp⟩
  have hPclean : SingularContinuation.TerminalCleanAt G P D :=
    fun p hp ↦ hclean p hp.1
  have hRstart : (G.quotient D).initialSet R ⊆ D := by
    rintro x ⟨q, hqR, hqx⟩
    have hxU : x ∈ (G.quotient D).initialSet U := ⟨q, hqR.1, hqx⟩
    rw [hE.linkage.initialSet_eq, hD.quotient_source_eq] at hxU
    exact hxU
  exact SingularContinuation.frozenPendingContinuation
    G (frozenAt G W E) hProof hD.stopover.minimal hPclean R hRstart

/-- The old row routes the original request set `B` to the quotient request
set `A` when every requested old component ends at a member of `A`. -/
def RoutesTerminals (G : DWeb V) (W : Set G.DPath)
    (B A : Set V) : Prop :=
  ∀ b ∈ B, ∃ f : DirectedPath.FinitePath G.graph,
    (Sum.inl f : G.DPath) ∈ W ∧ f.start = b ∧ f.finish ∈ A

/-- Target-link composition for the safe part of quotient re-entry.  If
all requested quotient starts lie outside the new stop-over, restriction to
`quotientPending` keeps every lower target witness, so source star transports
those witnesses back to the original requested ambient components. -/
theorem linksToTarget_frozenRestrictedContinuation
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : SingularContinuation.TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E)
    {A B : Set V} (hB : B ⊆ G.source)
    (hA : A ⊆ (G.quotient D).source) (hAE : A ⊆ Eᶜ)
    (hroute : RoutesTerminals G W B A)
    (hlinks : LinksToTarget (G.quotient D) U A) :
    LinksToTarget G
      (frozenRestrictedContinuation G hD hclean hE) B := by
  intro b hb
  obtain ⟨f, hfW, hfStart, hfFinishA⟩ := hroute b hb
  let P := pendingAt G W E
  let R := quotientPending G D E U
  have hfFinishNotE : f.finish ∉ E := hAE hfFinishA
  have hfP : (Sum.inl f : G.DPath) ∈ P := by
    refine ⟨hfW, ?_⟩
    rintro ⟨_hfW, e, heE, hfterm⟩
    exact hfFinishNotE (Option.some.inj hfterm ▸ heE)
  obtain ⟨p, hpU, q, hpq, hpure, before, after, hsupport,
    t, htTarget, htAfter⟩ := hlinks f.finish hfFinishA
  have hpq' : p = (Sum.inl q : (G.quotient D).DPath) := hpq
  subst p
  have hfinishQ : f.finish ∈ q.support := by
    have hsingleton : f.finish ∈ ({f.finish} : Set V) :=
      Set.mem_singleton f.finish
    rw [← hpure] at hsingleton
    exact hsingleton.1
  have hfinishInitial : f.finish ∈ (G.quotient D).initialSet U := by
    rw [hE.linkage.initialSet_eq]
    exact hA hfFinishA
  obtain ⟨q₀, hq₀U, hq₀Initial⟩ := hfinishInitial
  have hq₀eq : q₀ = (Sum.inl q : (G.quotient D).DPath) := by
    by_contra hne
    exact Set.disjoint_left.1
      (hE.linkage.isWarp hq₀U hpU hne)
      (hq₀Initial.symm ▸ q₀.initial_mem_support) hfinishQ
  subst q₀
  have hqStart : q.start = f.finish := hq₀Initial
  have hqR : (Sum.inl q : (G.quotient D).DPath) ∈ R := by
    refine ⟨hpU, ?_⟩
    change q.start ∉ E
    exact hqStart ▸ hfFinishNotE
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    SingularContinuation.linkage_vertexSet_subset_roof
      G hD.linkage hD.separator hclean
  have hProof : G.vertexSet P ⊆ G.roof D := by
    rintro x ⟨r, hr, hxr⟩
    exact hWroof ⟨r, hr.1, hxr⟩
  have hPclean : SingularContinuation.TerminalCleanAt G P D :=
    fun r hr ↦ hclean r hr.1
  have hRstart : (G.quotient D).initialSet R ⊆ D := by
    rintro x ⟨r, hr, hrx⟩
    have hxU : x ∈ (G.quotient D).initialSet U := ⟨r, hr.1, hrx⟩
    rw [hE.linkage.initialSet_eq, hD.quotient_source_eq] at hxU
    exact hxU
  let L := SingularContinuation.liftedQuotientFamily G D R
  have hcompat : G.StarCompatible P L :=
    SingularContinuation.starCompatible_liftQuotientFamily_of_roof
      G hProof hD.stopover.minimal hPclean hRstart
  let qLift : G.DPath := G.liftQuotientPath D (.inl q)
  have hqLiftL : qLift ∈ L := ⟨.inl q, hqR, rfl⟩
  have hqLiftInitial : qLift.initial = f.finish := by
    change q.start = f.finish
    exact hqStart
  have hmatch : ∃ r ∈ L, r.initial = f.finish :=
    ⟨qLift, hqLiftL, hqLiftInitial⟩
  let chosen : G.DPath := Classical.choose hmatch
  have hchosenL : chosen ∈ L := (Classical.choose_spec hmatch).1
  have hchosenInitial : chosen.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hLwarp : G.IsWarp L := by
    apply DWeb.IsWarp.liftQuotientFamily G
    intro r hr s hs hrs
    exact hE.linkage.isWarp hr.1 hs.1 hrs
  have hchosenEq : chosen = qLift := by
    by_contra hne
    exact Set.disjoint_left.1 (hLwarp hchosenL hqLiftL hne)
      (hchosenInitial.symm ▸ chosen.initial_mem_support)
      (hqLiftInitial.symm ▸ qLift.initial_mem_support)
  let rStar : G.DPath := G.starPath hcompat ⟨.inl f, hfP⟩
  have hrPending : rStar ∈
      SingularContinuation.pendingContinuation
        G hProof hD.stopover.minimal hPclean R hRstart :=
    ⟨⟨.inl f, hfP⟩, rfl⟩
  have hrMem : rStar ∈
      frozenRestrictedContinuation G hD hclean hE := by
    change rStar ∈
      frozenAt G W E ∪
        SingularContinuation.pendingContinuation
          G hProof hD.stopover.minimal hPclean R hRstart
    exact Or.inr hrPending
  have htQ : t ∈ q.support := by
    change t ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before htAfter
  have htLift : t ∈ qLift.support := by
    dsimp only [qLift]
    rw [G.support_liftQuotientPath]
    exact htQ
  have htChosen : t ∈ chosen.support := hchosenEq ▸ htLift
  have htStar : t ∈ rStar.support := by
    dsimp only [rStar]
    simp only [DWeb.starPath]
    split
    next hmatch' =>
      let chosen' : G.DPath := Classical.choose hmatch'
      have hchosen'L : chosen' ∈ L :=
        (Classical.choose_spec hmatch').1
      have hchosen'Initial : chosen'.initial = f.finish :=
        (Classical.choose_spec hmatch').2
      have hchosen'Eq : chosen' = qLift := by
        by_contra hne
        exact Set.disjoint_left.1 (hLwarp hchosen'L hqLiftL hne)
          (hchosen'Initial.symm ▸ chosen'.initial_mem_support)
          (hqLiftInitial.symm ▸ qLift.initial_mem_support)
      have htChosen' : t ∈ chosen'.support := hchosen'Eq ▸ htLift
      have hchosen'Start : chosen'.initial = f.finish :=
        hchosen'Initial
      have hinter : f.support ∩ chosen'.support ⊆ {f.finish} :=
        by
          intro x hx
          have hx' := hcompat (.inl f) hfP chosen' hchosen'L x hx.1 hx.2
          exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      rw [DirectedPath.Path.support_appendFinite f chosen'
        hchosen'Start hinter]
      exact Or.inr htChosen'
    next hnone =>
      exact (hnone hmatch).elim
  have hPfinite : G.HasFiniteCharacter P := by
    intro r hr
    exact hD.linkage.finiteCharacter hr.1
  have hRfinite : (G.quotient D).HasFiniteCharacter R := by
    intro r hr
    exact hE.linkage.finiteCharacter hr.1
  have hPendingFinite : G.HasFiniteCharacter
      (SingularContinuation.pendingContinuation
        G hProof hD.stopover.minimal hPclean R hRstart) :=
    SingularContinuation.pendingContinuation_finiteCharacter
      G hPfinite hProof hD.stopover.minimal hPclean hRfinite hRstart
  obtain ⟨g, hrg⟩ := hPendingFinite hrPending
  have hgMem : (Sum.inl g : G.DPath) ∈
      frozenRestrictedContinuation G hD hclean hE := hrg ▸ hrMem
  have htG : t ∈ g.support := by
    rw [hrg] at htStar
    exact htStar
  have hgStart : g.start = b := by
    have hstart := G.initial_starPath hcompat ⟨(.inl f : G.DPath), hfP⟩
    dsimp only [rStar] at hrg
    rw [hrg] at hstart
    exact hstart.trans hfStart
  have htFinish : t = g.finish :=
    hNorm.eq_finish_of_mem_walk g.walk htG htTarget
  have hgSourcePure : g.support ∩ B = {b} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxg, hxB⟩
      exact Set.mem_singleton_iff.2
        ((hNorm.eq_start_of_mem_walk g.walk hxg (hB hxB)).trans hgStart)
    · intro x hx
      have hxb : x = b := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨?_, hb⟩
      exact hgStart ▸ g.start_mem_support
  refine ⟨.inl g, hgMem, g, rfl, hgSourcePure, ?_⟩
  refine ⟨[], g.walk.support.tail, ?_, g.finish, ?_, ?_⟩
  · simp only [List.nil_append]
    calc
      g.walk.support =
          g.walk.support.head g.walk.support_ne_nil :: g.walk.support.tail :=
        (g.walk.support.cons_head_tail g.walk.support_ne_nil).symm
      _ = b :: g.walk.support.tail := by
        congr 1
        rw [g.walk.head_support]
        exact hgStart
  · exact htFinish ▸ htTarget
  · have hcons : b :: g.walk.support.tail = g.walk.support := by
      calc
        b :: g.walk.support.tail =
            g.walk.support.head g.walk.support_ne_nil ::
              g.walk.support.tail := by
                exact congrArg (fun x ↦ x :: g.walk.support.tail)
                  (g.walk.head_support.trans hgStart).symm
        _ = g.walk.support :=
          g.walk.support.cons_head_tail g.walk.support_ne_nil
    change g.finish ∈ b :: g.walk.support.tail
    rw [hcons]
    exact g.finish_mem_support

/-- The genuine future-safe quotient re-entry step.  Old members already
ending in `E` are frozen; all other old members are continued only with
quotient paths whose initial vertex lies outside `E`.  The result is a
finite full warp, an honest forward extension, and a terminal-clean
half-way linkage with ambient stop-over `E`. -/
theorem frozenRestrictedContinuation_structural
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : SingularContinuation.TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    IsSeparatingHalfwayStopover G
        (frozenRestrictedContinuation G hD hclean hE) E ∧
      SingularContinuation.TerminalCleanAt G
        (frozenRestrictedContinuation G hD hclean hE) E ∧
      G.ForwardExtension W
        (frozenRestrictedContinuation G hD hclean hE) ∧
      G.initialSet (frozenRestrictedContinuation G hD hclean hE) =
        G.source := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  let F : Set G.DPath := frozenAt G W E
  let P : Set G.DPath := pendingAt G W E
  let R : Set (G.quotient D).DPath := quotientPending G D E U
  have hFsub : F ⊆ W := fun _ hp ↦ hp.1
  have hPsub : P ⊆ W := fun _ hp ↦ hp.1
  have hRsub : R ⊆ U := fun _ hp ↦ hp.1
  have hFwarp : G.IsWarp F := by
    intro p hp q hq hpq
    exact hD.linkage.isWarp (hFsub hp) (hFsub hq) hpq
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact hD.linkage.isWarp (hPsub hp) (hPsub hq) hpq
  have hRwarp : (G.quotient D).IsWarp R := by
    intro p hp q hq hpq
    exact hE.linkage.isWarp (hRsub hp) (hRsub hq) hpq
  have hFfinite : G.HasFiniteCharacter F := by
    intro p hp
    exact hD.linkage.finiteCharacter (hFsub hp)
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hD.linkage.finiteCharacter (hPsub hp)
  have hRfinite : (G.quotient D).HasFiniteCharacter R := by
    intro p hp
    exact hE.linkage.finiteCharacter (hRsub hp)
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    SingularContinuation.linkage_vertexSet_subset_roof
      G hD.linkage hD.separator hclean
  have hProof : G.vertexSet P ⊆ G.roof D := by
    rintro x ⟨p, hp, hxp⟩
    exact hWroof ⟨p, hPsub hp, hxp⟩
  have hPclean : SingularContinuation.TerminalCleanAt G P D :=
    fun p hp ↦ hclean p (hPsub hp)
  have hRstart : (G.quotient D).initialSet R ⊆ D := by
    rintro x ⟨q, hqR, hqx⟩
    have hxU : x ∈ (G.quotient D).initialSet U :=
      ⟨q, hRsub hqR, hqx⟩
    rw [hE.linkage.initialSet_eq, hD.quotient_source_eq] at hxU
    exact hxU
  have hcover : G.terminalFrontier P ⊆
      (G.quotient D).initialSet R := by
    rintro x ⟨p, hpP, hpx⟩
    have hxD : x ∈ D := hD.linkage.terminalFrontier_subset
      ⟨p, hPsub hpP, hpx⟩
    have hxSource : x ∈ (G.quotient D).source := by
      rw [hD.quotient_source_eq]
      exact hxD
    have hxInitial : x ∈ (G.quotient D).initialSet U := by
      rw [hE.linkage.initialSet_eq]
      exact hxSource
    obtain ⟨q, hqU, hqx⟩ := hxInitial
    have hxNotE : x ∉ E := by
      intro hxE
      apply hpP.2
      exact ⟨hPsub hpP, x, hxE, hpx⟩
    exact ⟨q, ⟨hqU, hqx ▸ hxNotE⟩, hqx⟩
  have hFP : Disjoint (G.vertexSet F) (G.vertexSet P) := by
    apply Set.disjoint_left.2
    intro x hxF hxP
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqP, hxq⟩ := hxP
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hqP.2 hpF
    exact Set.disjoint_left.1
      (hD.linkage.isWarp (hFsub hpF) (hPsub hqP) hpq) hxp hxq
  have hFR : Disjoint (G.vertexSet F)
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G D R)) := by
    have hcompat :=
      SingularContinuation.starCompatible_liftQuotientFamily_of_roof
        G hWroof hD.stopover.minimal hclean hRstart
    apply Set.disjoint_left.2
    intro x hxF hxR
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqLift, hxq⟩ := hxR
    have hxGlue := hcompat p (hFsub hpF) q hqLift x hxp hxq
    obtain ⟨e, heE, hpterm⟩ := hpF.2
    have hxe : x = e := Option.some.inj (hxGlue.1.symm.trans hpterm)
    obtain ⟨q₀, hq₀R, rfl⟩ := hqLift
    have hqStartNotE : q₀.initial ∉ E := hq₀R.2
    apply hqStartNotE
    rw [G.initial_liftQuotientPath] at hxGlue
    exact hxGlue.2.symm ▸ hxe ▸ heE
  let W' : Set G.DPath :=
    SingularContinuation.frozenPendingContinuation
      G F hProof hD.stopover.minimal hPclean R hRstart
  have hW'warp : G.IsWarp W' :=
    SingularContinuation.frozenPendingContinuation_isWarp
      G hFwarp hPwarp hProof hD.stopover.minimal hPclean
        hRwarp hRstart
        (SingularContinuation.disjoint_vertexSet_pendingContinuation
          G hProof hD.stopover.minimal hPclean R hRstart hFP hFR)
  have hW'finite : G.HasFiniteCharacter W' :=
    SingularContinuation.frozenPendingContinuation_finiteCharacter
      G hFfinite hPfinite hProof hD.stopover.minimal hPclean
        hRfinite hRstart
  have hforwardFP : G.ForwardExtension (F ∪ P) W' :=
    SingularContinuation.forwardExtension_frozenPendingContinuation
      G F hProof hD.stopover.minimal hPclean R hRstart
  have hforward : G.ForwardExtension W W' := by
    rw [← frozenAt_union_pendingAt G W E]
    exact hforwardFP
  have hinitial : G.initialSet W' = G.source := by
    rw [← hD.linkage.initialSet_eq]
    exact (G.initialSet_eq_of_forwardExtension hforward).symm
  have hterminal : G.terminalFrontier W' ⊆ E := by
    have hfront : G.terminalFrontier W' ⊆
        G.terminalFrontier F ∪ (G.quotient D).terminalFrontier R :=
      SingularContinuation.terminalFrontier_frozenPendingContinuation_subset
        (F := F) G hPfinite hProof hD.stopover.minimal hPclean
          hRstart hcover
    intro x hx
    rcases hfront hx with hxF | hxR
    · obtain ⟨p, hpF, hpx⟩ := hxF
      obtain ⟨e, heE, hpterm⟩ := hpF.2
      exact Option.some.inj (hpx.symm.trans hpterm) ▸ heE
    · exact hE.linkage.terminalFrontier_subset
        ⟨hxR.choose, hRsub hxR.choose_spec.1, hxR.choose_spec.2⟩
  have hFboundary : SliceSpliceSource.MeetsOnlyAtTerminal G F E :=
    frozenAt_terminalClean hNoEnter hD hclean hE
  have hPboundary : SliceSpliceSource.MeetsOnlyAtTerminal G P E := by
    intro p hp x hxp hxE
    exact False.elim (Set.disjoint_left.1
      (pendingAt_disjoint_newStopover hNoEnter hD hclean hE)
      ⟨p, hp, hxp⟩ hxE)
  have hLboundary : SliceSpliceSource.MeetsOnlyAtTerminal G
      (SingularContinuation.liftedQuotientFamily G D R) E :=
    lifted_quotientPending_terminalClean hE
  have hcompat : G.StarCompatible P
      (SingularContinuation.liftedQuotientFamily G D R) :=
    SingularContinuation.starCompatible_liftQuotientFamily_of_roof
      G hProof hD.stopover.minimal hPclean hRstart
  have hcoverLift : G.terminalFrontier P ⊆
      G.initialSet (SingularContinuation.liftedQuotientFamily G D R) := by
    simpa only [G.initialSet_liftQuotientFamily] using hcover
  have hPendingBoundary : SliceSpliceSource.MeetsOnlyAtTerminal G
      (SingularContinuation.pendingContinuation
        G hProof hD.stopover.minimal hPclean R hRstart) E := by
    exact SliceSpliceSource.meetsOnlyAtTerminal_star
      hPfinite hPboundary hLboundary hcompat hcoverLift
  have hW'boundary : SliceSpliceSource.MeetsOnlyAtTerminal G W' E := by
    intro p hp
    exact hp.elim (hFboundary p) (hPendingBoundary p)
  have hTight : SliceSpliceSource.TightLinkageBetween
      G G.source E W' :=
    SliceSpliceSource.tightLinkageBetween_of_structural
      hNorm Set.Subset.rfl hW'warp hW'finite hinitial hterminal hW'boundary
  change IsSeparatingHalfwayStopover G W' E ∧
    SingularContinuation.TerminalCleanAt G W' E ∧
    G.ForwardExtension W W' ∧ G.initialSet W' = G.source
  refine ⟨?_, hW'boundary, hforward, hinitial⟩
  exact ⟨⟨hTight.1, newStopover_isTrimmed hNoEnter hD hE,
      quotient_new_isUnhindered hNoEnter hD hE⟩,
    newStopover_isSeparator hD hE.separator⟩

/-- Existential wrapper retained for callers which do not need the concrete
name of the future-safe row. -/
theorem exists_frozenRestrictedContinuation
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : SingularContinuation.TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    ∃ W' : Set G.DPath,
      IsSeparatingHalfwayStopover G W' E ∧
      SingularContinuation.TerminalCleanAt G W' E ∧
      G.ForwardExtension W W' ∧
      G.initialSet W' = G.source := by
  exact ⟨frozenRestrictedContinuation G hD hclean hE,
    frozenRestrictedContinuation_structural hNorm hD hclean hE⟩

/-- Complete quotient re-entry from the lower-cardinal half-way witness.
The local height bound remains a bound in the quotient where the lower
half-way theorem was applied; the ambient conclusion is the exact data
needed for the next geometric state: a separating terminal-clean stop-over,
an unhindered ambient quotient, and a forward-extended finite full warp. -/
theorem exists_reenteredContinuation_of_halfway
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : SingularContinuation.TerminalCleanAt G W D)
    {A : Set V} {kappa : Cardinal.{u}}
    {U : Set (G.quotient D).DPath}
    (hU : IsHalfwayLinkageOfAltitude (G.quotient D) A kappa U) :
    ∃ (E : Set V) (W' : Set G.DPath),
      IsSeparatingHalfwayStopover (G.quotient D) U E ∧
      HeightAtMost (G.quotient D) E kappa ∧
      IsSeparatingHalfwayStopover G W' E ∧
      SingularContinuation.TerminalCleanAt G W' E ∧
      G.ForwardExtension W W' ∧
      G.initialSet W' = G.source := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  obtain ⟨C, hC, hheightC⟩ := hU.exists_stopover
  obtain ⟨E, hE, hheightE, _hEsub, _hquotient⟩ :=
    exists_quotientSeparatingStopover hNoEnter hC hheightC
  obtain ⟨W', hW', hW'clean, hforward, hinitial⟩ :=
    exists_frozenRestrictedContinuation hNorm hD hclean hE
  exact ⟨E, W', hE, hheightE, hW', hW'clean, hforward, hinitial⟩

end SingularQuotientReentry
end CardinalInduction
end Erdos599
