/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularLiteralColumnContinuation
import ErdosProblems.Erdos599.SingularSafeBatch

/-!
# Source-disjoint half-way stop-overs and literal quotient continuation

Definition 2.23 of Aharoni--Berger forms the quotient only at a set
`C \subseteq V \ A`.  The core `IsHalfwayStopover` record predates that
typing condition, so this file records it locally without changing the
existing public structure.

The extra condition removes the apparent need to freeze old paths during a
successor step.  A proper new stop-over in the old quotient is disjoint from
the old quotient source, hence from the old stop-over.  Separation and
trimmedness then show that it is disjoint from the entire old row.  Thus no
old path is frozen and no quotient path is discarded; the ordinary
source-star continuation is the literal successor operation used in
Assertion 9.17.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProperHalfwayContinuation

open SingularBoundarySplit SingularContinuation SingularQuotientReentry
  SingularTargetLinkTransfer

universe u

variable {V : Type u}

/-- A half-way stop-over satisfying the source-disjointness condition which
is part of the domain of the quotient operation in Definition 2.23 of the
source paper. -/
structure ProperHalfwayStopover (G : DWeb V)
    (W : Set G.DPath) (C : Set V) : Prop where
  separating : IsSeparatingHalfwayStopover G W C
  source_disjoint : Disjoint G.source C

namespace ProperHalfwayStopover

theorem linkage {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (h : ProperHalfwayStopover G W C) :
    IsLinkageBetween G G.source C W :=
  h.separating.linkage

theorem terminalClean {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (h : ProperHalfwayStopover G W C) :
    TerminalCleanAt G W C :=
  terminalCleanAt_of_linkage_of_disjoint G h.linkage h.source_disjoint

theorem quotient_source_eq {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (h : ProperHalfwayStopover G W C) :
    (G.quotient C).source = C :=
  h.separating.quotient_source_eq

theorem quotient_unhindered {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (h : ProperHalfwayStopover G W C) :
    (G.quotient C).IsUnhindered :=
  h.separating.quotient_unhindered

end ProperHalfwayStopover

/-- The slightly sharper invariant requested by the source proof is already
enough for terminal cleanliness: a component whose initial vertex is also
on the boundary must be the trivial component.  This formulation is useful
when a construction has not yet proved literal disjointness. -/
theorem terminalCleanAt_of_boundary_starts_trivial
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (htrivial : ∀ p ∈ W, p.initial ∈ C →
      p = G.trivialPath p.initial) :
    TerminalCleanAt G W C := by
  intro p hp x hxp hxC
  obtain ⟨f, rfl, hends, _hsource⟩ := hW.endpointPure p hp
  have hxEnds : x ∈ ({f.start, f.finish} : Set V) := by
    rw [← hends]
    exact ⟨hxp, Or.inr hxC⟩
  rcases Set.mem_insert_iff.1 hxEnds with hxStart | hxFinish
  · have hstartC : f.start ∈ C := hxStart ▸ hxC
    have heq := htrivial (.inl f) hp hstartC
    rw [heq, G.terminal?_trivialPath]
    exact congrArg some hxStart.symm
  · change some f.finish = some x
    exact congrArg some (Set.mem_singleton_iff.1 hxFinish).symm

/-- A proper stop-over chosen in the old quotient cannot meet the carrier of
the old row.  The point is geometric: the old carrier is roofed by `D`, the
new stop-over avoids the old strict roof, and properness excludes the only
remaining possibility, namely membership in `D` itself. -/
theorem disjoint_oldCarrier_newStopover
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    Disjoint (G.vertexSet W) E := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hroof : G.vertexSet W ⊆ G.roof D :=
    linkage_vertexSet_subset_roof G hD.linkage
      hD.separating.separator hD.terminalClean
  have hstrict : Disjoint E (G.strictRoof D) :=
    disjoint_newStopover_strictRoof_old hNoEnter
      hD.separating hE.separating
  apply Set.disjoint_left.2
  intro x hxW hxE
  have hxRoof : x ∈ G.roof D := hroof hxW
  have hxNotStrict : x ∉ G.strictRoof D := by
    intro hxStrict
    exact Set.disjoint_left.1 hstrict hxE hxStrict
  have hxEssential : x ∈ G.essential D := by
    by_contra hxNotEssential
    exact hxNotStrict ⟨hxRoof, hxNotEssential⟩
  have hxD : x ∈ D := by
    rw [← hD.separating.stopover.minimal]
    exact hxEssential
  have hxSource : x ∈ (G.quotient D).source := by
    rw [hD.quotient_source_eq]
    exact hxD
  exact Set.disjoint_left.1 hE.source_disjoint hxSource hxE

/-- Properness is inherited by the ambient stop-over after quotient
re-entry. -/
theorem ambientSource_disjoint_newStopover
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    Disjoint G.source E := by
  have hcarrier : Disjoint (G.vertexSet W) E :=
    disjoint_oldCarrier_newStopover hNorm hD hE
  apply Set.disjoint_left.2
  intro x hxSource hxE
  have hxInitial : x ∈ G.initialSet W := by
    rw [hD.linkage.initialSet_eq]
    exact hxSource
  obtain ⟨p, hpW, hpx⟩ := hxInitial
  exact Set.disjoint_left.1 hcarrier
    ⟨p, hpW, hpx.symm ▸ p.initial_mem_support⟩ hxE

/-- Under properness no old path is frozen at the next stop-over. -/
theorem frozenAt_eq_empty
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    frozenAt G W E = ∅ := by
  have hdis : Disjoint (G.vertexSet W) E :=
    disjoint_oldCarrier_newStopover hNorm hD hE
  ext p
  constructor
  · intro hp
    obtain ⟨hpW, e, heE, hpterm⟩ := hp
    exact (Set.disjoint_left.1 hdis
      ⟨p, hpW, G.terminal_mem_support hpterm⟩ heE).elim
  · exact False.elim

/-- Under properness every old path remains pending. -/
theorem pendingAt_eq
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    pendingAt G W E = W := by
  ext p
  simp only [pendingAt, Set.mem_sdiff]
  rw [frozenAt_eq_empty hNorm hD hE]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, and_true]

/-- Under properness no quotient path is discarded by the future-safe
restriction. -/
theorem quotientPending_eq
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (_hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    quotientPending G D E U = U := by
  apply Set.Subset.antisymm (quotientPending_subset G D E U)
  intro p hpU
  refine ⟨hpU, ?_⟩
  have hpSource : p.initial ∈ (G.quotient D).source := by
    rw [← hE.linkage.initialSet_eq]
    exact ⟨p, hpU, rfl⟩
  exact Set.disjoint_left.1 hE.source_disjoint hpSource

/-- Lifted members of a proper quotient stop-over meet the new boundary only
at their terminal. -/
theorem liftedQuotientFamily_terminalClean
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (_hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    TerminalCleanAt G (liftedQuotientFamily G D U) E := by
  intro p hp x hxp hxE
  obtain ⟨q, hqU, rfl⟩ := hp
  have hxq : x ∈ q.support := by
    simpa only [G.support_liftQuotientPath] using hxp
  have hterm := hE.terminalClean q hqU x hxq hxE
  simpa only [G.terminal?_liftQuotientPath] using hterm

/-- The literal source-star continuation meets a proper next stop-over only
at its terminal. -/
theorem continuation_terminalClean
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    TerminalCleanAt G
      (continuation G hD.linkage hD.separating.separator
        hD.separating.stopover.minimal hD.terminalClean U
          hE.linkage.initialSet_eq) E := by
  let L : Set G.DPath := liftedQuotientFamily G D U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_linkage G hD.linkage
      hD.separating.separator hD.separating.stopover.minimal
        hD.terminalClean hE.linkage.initialSet_eq
  have hWboundary : SliceSpliceSource.MeetsOnlyAtTerminal G W E := by
    have hdis := disjoint_oldCarrier_newStopover hNorm hD hE
    intro p hp x hxp hxE
    exact False.elim (Set.disjoint_left.1 hdis ⟨p, hp, hxp⟩ hxE)
  have hLboundary : SliceSpliceSource.MeetsOnlyAtTerminal G L E :=
    liftedQuotientFamily_terminalClean hD hE
  have hcover : G.terminalFrontier W ⊆ G.initialSet L := by
    change G.terminalFrontier W ⊆
      G.initialSet (G.liftQuotientFamily D U)
    rw [G.initialSet_liftQuotientFamily]
    exact terminalFrontier_subset_quotientInitialSet_of_linkage G
      hD.separating.separator hD.separating.stopover.minimal
        hD.linkage.terminalFrontier_subset hE.linkage
  exact SliceSpliceSource.meetsOnlyAtTerminal_star
    hD.linkage.finiteCharacter hWboundary hLboundary hc hcover

/-- Proper stop-overs are closed under literal quotient continuation.  This
is the direct iteration endpoint which is unavailable from the present weak
`IsHalfwayStopover` API. -/
theorem continuation_properStopover
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : ProperHalfwayStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ProperHalfwayStopover (G.quotient D) U E) :
    ProperHalfwayStopover G
      (continuation G hD.linkage hD.separating.separator
        hD.separating.stopover.minimal hD.terminalClean U
          hE.linkage.initialSet_eq) E := by
  let P : Set G.DPath := continuation G hD.linkage
    hD.separating.separator hD.separating.stopover.minimal
      hD.terminalClean U hE.linkage.initialSet_eq
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hPwarp : G.IsWarp P := continuation_isWarp G hD.linkage
    hD.separating.separator hD.separating.stopover.minimal
      hD.terminalClean hE.linkage.isWarp hE.linkage.initialSet_eq
  have hPfinite : G.HasFiniteCharacter P :=
    continuation_finiteCharacter G hD.linkage hD.separating.separator
      hD.separating.stopover.minimal hD.terminalClean
        hE.linkage.finiteCharacter hE.linkage.initialSet_eq
  have hPinitial : G.initialSet P = G.source :=
    initialSet_continuation G hD.linkage hD.separating.separator
      hD.separating.stopover.minimal hD.terminalClean U
        hE.linkage.initialSet_eq
  have hPterminal : G.terminalFrontier P ⊆ E := by
    have hfront := terminalFrontier_continuation_subset G hD.linkage
      hD.separating.separator hD.separating.stopover.minimal
        hD.terminalClean hE.linkage.initialSet_eq
    rw [G.terminalFrontier_liftQuotientFamily] at hfront
    exact hfront.trans hE.linkage.terminalFrontier_subset
  have hPclean : SliceSpliceSource.MeetsOnlyAtTerminal G P E :=
    continuation_terminalClean hNorm hD hE
  have hlink : IsLinkageBetween G G.source E P :=
    (SliceSpliceSource.tightLinkageBetween_of_structural hNorm
      Set.Subset.rfl hPwarp hPfinite hPinitial hPterminal hPclean).1
  have hseparating : IsSeparatingHalfwayStopover G P E :=
    ⟨⟨hlink, newStopover_isSeparator hD.separating hE.separating.separator,
      newStopover_isTrimmed hNoEnter hD.separating hE.separating,
      quotient_new_isUnhindered hNoEnter hD.separating hE.separating⟩,
      newStopover_isSeparator hD.separating hE.separating.separator⟩
  exact ⟨hseparating,
    ambientSource_disjoint_newStopover hNorm hD hE⟩

/-- A literal proper successor row.  Unlike the general future-safe splice,
the displayed family is the ordinary `continuation` of Assertion 9.17. -/
structure ProperColumnSuccessor
    (G : DWeb V) {W : Set G.DPath} {D B : Set V}
    (hD : ProperHalfwayStopover G W D)
    (rho : Cardinal.{u}) where
  quotientPaths : Set (G.quotient D).DPath
  quotientHalfway : IsHalfwayLinkageOfAltitude
    (G.quotient D) (requestedFrontier G W B) rho quotientPaths
  quotientBoundary : Set V
  quotientProper : ProperHalfwayStopover
    (G.quotient D) quotientPaths quotientBoundary
  quotientHeight : HeightAtMost
    (G.quotient D) quotientBoundary rho
  paths : Set G.DPath
  paths_eq : paths = continuation G hD.linkage
    hD.separating.separator hD.separating.stopover.minimal
      hD.terminalClean quotientPaths quotientProper.linkage.initialSet_eq
  ambientProper : ProperHalfwayStopover G paths quotientBoundary
  forward : G.ForwardExtension W paths
  links : LinksToTarget G paths B

/-- The exact one-step endpoint.  The only additional producer input beyond
the present `HalfwayClauseAt` API is that its selected altitude-realizing
stop-over in the quotient is source-disjoint. -/
noncomputable def properColumnSuccessor_of_quotientWitness
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D B : Set V}
    (hD : ProperHalfwayStopover G W D)
    (hB : B ⊆ G.source)
    {rho : Cardinal.{u}}
    {U : Set (G.quotient D).DPath}
    (hU : IsHalfwayLinkageOfAltitude
      (G.quotient D) (requestedFrontier G W B) rho U)
    {E : Set V}
    (hE : ProperHalfwayStopover (G.quotient D) U E)
    (hheight : HeightAtMost (G.quotient D) E rho) :
    ProperColumnSuccessor G (B := B) hD rho := by
  let P : Set G.DPath := continuation G hD.linkage
    hD.separating.separator hD.separating.stopover.minimal
      hD.terminalClean U hE.linkage.initialSet_eq
  have hambient : ProperHalfwayStopover G P E :=
    continuation_properStopover hNorm hD hE
  have hAsource : requestedFrontier G W B ⊆
      (G.quotient D).source := by
    rw [hD.quotient_source_eq]
    rintro x ⟨p, hp, hpx⟩
    exact hD.linkage.terminalFrontier_subset ⟨p, hp.1, hpx⟩
  have hPlinks : LinksToTarget G P B :=
    linksToTarget_continuation hNorm hD.separating hD.terminalClean
      hE.linkage.isWarp hE.linkage.finiteCharacter
      hE.linkage.initialSet_eq hAsource hB
      (SingularLiteralColumnContinuation.routes_terminalRequest
        hD.separating hB) hU.2.1
  exact {
    quotientPaths := U
    quotientHalfway := hU
    quotientBoundary := E
    quotientProper := hE
    quotientHeight := hheight
    paths := P
    paths_eq := rfl
    ambientProper := hambient
    forward := forwardExtension_continuation G hD.linkage
      hD.separating.separator hD.separating.stopover.minimal
        hD.terminalClean U hE.linkage.initialSet_eq
    links := hPlinks
  }

/-- The precise missing producer refinement.  It strengthens only the
choice of stop-over attached to the ordinary lower half-way linkage. -/
def ProperHalfwayClauseAt (G : DWeb V) (rho : Cardinal.{u}) : Prop :=
  ∀ A : Set V, A ⊆ G.source → #A = rho →
    ∃ (U : Set G.DPath) (E : Set V),
      IsHalfwayLinkageOfAltitude G A rho U ∧
      ProperHalfwayStopover G U E ∧ HeightAtMost G E rho

/-- Forgetting the source-disjoint witness recovers the existing public
half-way clause. -/
theorem ProperHalfwayClauseAt.toHalfwayClauseAt
    {G : DWeb V} {rho : Cardinal.{u}}
    (h : ProperHalfwayClauseAt G rho) : HalfwayClauseAt G rho := by
  intro A hA hcard
  obtain ⟨U, _E, hU, _hE, _hheight⟩ := h A hA hcard
  exact ⟨U, hU⟩

/-- A proper lower half-way clause produces the literal successor row after
the terminal-coordinate change. -/
theorem exists_properColumnSuccessor
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D B : Set V}
    (hD : ProperHalfwayStopover G W D)
    (hB : B ⊆ G.source) {rho : Cardinal.{u}}
    (hBcard : #B = rho)
    (hlowerProper : ProperHalfwayClauseAt (G.quotient D) rho) :
    Nonempty (ProperColumnSuccessor G (B := B) hD rho) := by
  let A : Set V := requestedFrontier G W B
  have hAsource : A ⊆ (G.quotient D).source := by
    rw [hD.quotient_source_eq]
    rintro x ⟨p, hp, hpx⟩
    exact hD.linkage.terminalFrontier_subset ⟨p, hp.1, hpx⟩
  have hAcard : #A = rho := by
    dsimp only [A]
    rw [SingularLiteralColumnContinuation.terminalRequest_card
      hD.separating hB, hBcard]
  obtain ⟨U, E, hU, hE, hheight⟩ :=
    hlowerProper A hAsource hAcard
  exact ⟨properColumnSuccessor_of_quotientWitness
    hNorm hD hB hU hE hheight⟩

/-- The existing lower half-way output does not expose the properness field.
This is the exact refinement obligation for `FullSourceBatch`: its selected
boundary must be disjoint from the source of the web in which the batch was
constructed. -/
def FullSourceBatchProper
    {H : DWeb V} {current : Set V} {rho : Cardinal.{u}}
    (B : SingularSafeBatch.FullSourceBatch H current rho) : Prop :=
  Disjoint H.source B.boundary

/-- A full-source batch carrying the source-disjoint field which is needed
for literal iteration. -/
structure ProperFullSourceBatch
    (H : DWeb V) (current : Set V) (rho : Cardinal.{u}) where
  batch : SingularSafeBatch.FullSourceBatch H current rho
  proper : FullSourceBatchProper batch

/-- The refined half-way clause produces a proper full-source batch with no
further geometric work. -/
theorem exists_properFullSourceBatch_of_clause
    {H : DWeb V} {current : Set V} {rho : Cardinal.{u}}
    (hcurrent : current ⊆ H.source) (hcard : #current = rho)
    (hproper : ProperHalfwayClauseAt H rho) :
    Nonempty (ProperFullSourceBatch H current rho) := by
  obtain ⟨U, E, hU, hE, hheight⟩ :=
    hproper current hcurrent hcard
  exact ⟨⟨⟨U, E, hU, hE.separating, hheight⟩,
    hE.source_disjoint⟩⟩

theorem fullSourceBatchProper_iff_proper
    {H : DWeb V} {current : Set V} {rho : Cardinal.{u}}
    (B : SingularSafeBatch.FullSourceBatch H current rho) :
    FullSourceBatchProper B ↔
      ProperHalfwayStopover H B.paths B.boundary := by
  exact ⟨fun h ↦ ⟨B.separating, h⟩, fun h ↦ h.source_disjoint⟩

/-- The hybrid half-way construction used by existing small-source and
linkable branches deliberately puts every unselected source into its
stop-over.  Hence that producer cannot satisfy Definition 2.23 properness
unless there are no unselected sources. -/
theorem hybridStopover_not_sourceDisjoint_of_unselected
    {G : DWeb V} {L : Set G.DPath} {A : Set V} {x : V}
    (hx : x ∈ G.source \ A) :
    ¬ Disjoint G.source (Hybrid.stopover G L A) := by
  intro hdis
  exact Set.disjoint_left.1 hdis hx.1 (Or.inl hx)

/-- Although the hybrid producer is generally not source-disjoint, it does
have the sharper viable invariant: its displayed stop-over is exactly its
terminal frontier.  Thus all source vertices which it deliberately leaves
on the boundary are represented by exposed trivial components. -/
theorem hybrid_warp_terminalFrontier_eq_stopover
    (G : DWeb V) (L : Set G.DPath) (A : Set V) :
    G.terminalFrontier (Hybrid.warp G L A) =
      Hybrid.stopover G L A := by
  apply Set.Subset.antisymm (Hybrid.warp_terminalFrontier_subset G)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨G.trivialPath x, ?_, G.terminal?_trivialPath x⟩
    exact Or.inr ⟨x, hx, rfl⟩
  · obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, Or.inl hp, hpx⟩

#print axioms terminalCleanAt_of_boundary_starts_trivial
#print axioms continuation_terminalClean
#print axioms continuation_properStopover
#print axioms properColumnSuccessor_of_quotientWitness
#print axioms exists_properColumnSuccessor
#print axioms fullSourceBatchProper_iff_proper
#print axioms exists_properFullSourceBatch_of_clause
#print axioms hybridStopover_not_sourceDisjoint_of_unselected
#print axioms hybrid_warp_terminalFrontier_eq_stopover

end SingularProperHalfwayContinuation
end CardinalInduction
end Erdos599
