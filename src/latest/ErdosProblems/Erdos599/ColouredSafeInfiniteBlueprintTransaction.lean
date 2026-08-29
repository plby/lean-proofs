/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageInfiniteSwitch
import ErdosProblems.Erdos599.ColouredSafeStrongSourceCoverage
import ErdosProblems.Erdos599.ColouredSafeOnePortSplice

/-!
# Actual native infinite-occurrence blueprint transaction

At an old finite terminal, insert the selected finite source component of
an infinite-occurrence switch and every reference-source companion. Exact
one-port geometry preserves all six native conditions and gives a real
path into the stage frontier. No uniform roof or fair-limit theorem is
inferred from this local construction.
-/

noncomputable section

namespace Erdos599.ColouredSafeAmbientOccurrence.TouchedInfiniteSwitch

open Set Cardinal Order DirectedPath Ladder Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s : V}
variable {A : Occurrence Y s}

theorem initials_sdiff_source (T : TouchedInfiniteSwitch A)
    (hs : s ∉ Gamma.vertexSet Y) :
    Gamma.initialSet T.paths \ {s} = Gamma.initialSet A.touchedReference := by
  rw [T.initials]
  have hsLocal : s ∉ Gamma.initialSet A.touchedReference := by
    rintro ⟨p, hp, hps⟩
    exact hs ⟨p, hp.1, hps ▸ p.initial_mem_support⟩
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact hx
    · exact False.elim (hne hx)
  · intro hx
    exact ⟨Or.inl hx, fun hxs ↦ hsLocal (hxs ▸ hx)⟩

theorem limitOwner_initial_mem_touchedReference_of_meets
    {rho : Cardinal.{u}} {L : Gamma.KappaLadder rho} {a : Stage rho}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {A : Occurrence L.limitWarp s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedInfiniteSwitch (A.retypeStageReference hL hARoof))
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hfrontier : (p.support ∩ L.frontier a).Nonempty)
    (hmeet : (p.support ∩ Gamma.vertexSet T.paths).Nonempty) :
    p.initial ∈ Gamma.initialSet (A.retypeStageReference hL hARoof).touchedReference := by
  obtain ⟨v, hvp, hvFrontier⟩ := hfrontier
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    LinkageBlueprint.ladderReference.exists_prefix_of_limitWarp_frontier_hit
      hL hp hvFrontier hvp
  obtain ⟨x, hxp, hxT⟩ := hmeet
  have hxq : x ∈ q.support :=
    DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      hL a hp hq.1 hqp ⟨hxp, hTRoof hxT⟩
  have hqTouched :=
    (A.retypeStageReference hL hARoof).mem_touchedReference_of_meets_referenceClosure
      (hL.warpStages (Stage.toExtended a)) hq.1 ⟨x, hxq, T.carrier_subset hxT⟩
  exact ⟨q, hqTouched, Gamma.extends_initial hqp⟩

end Erdos599.ColouredSafeAmbientOccurrence.TouchedInfiniteSwitch

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem exists_infiniteBlueprintTransaction
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V} (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s : V} (hsTerminal : s ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s none extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hclosed : ∀ A, extra A → A.vertexSet ⊆ Z) :
    ∃ (p : FinitePath Gamma.graph)
      (U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath),
      p.start = s ∧ p.finish ∈ C.ladder.frontier a ∧
      p.edgeSet ⊆ familyEdges U ∧
      p.support ⊆ (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ∧
      IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
      (imaginaryWeb C.ladder.limitWarp kappa).initialSet W ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).initialSet U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ⊆
        (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ⊆
        ((imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W \ {s}) ∪
          C.ladder.frontier a := by
  let G := imaginaryWeb C.ladder.limitWarp kappa
  have hWcard : #(G.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  obtain ⟨A, hA, hARoof, T, hTX, _hcompX, hTRoof, hEss, hfinish⟩ :=
    C.native_global_hasCard_exists_infiniteTouchedSwitch_avoiding ha h hroof hWcard
  have hs : s ∉ Gamma.vertexSet (C.ladder.warpAt a) := by
    rintro ⟨p, hp, hsp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact hA.2.2.1
      ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2, E.support_subset ⟨p, hp⟩ hsp⟩
  let ps : FinitePath G.graph := T.sourcePath.lift (fun he ↦ Or.inl he)
  have hps : ps.start = s := T.source_start
  have hpsK : Sum.inl ps ∈ liftRealFamily (Y := C.ladder.limitWarp) (kappa := kappa) T.paths :=
    ⟨.inl T.sourcePath, T.source_mem, rfl⟩
  have hKinter : G.vertexSet (liftRealFamily T.paths) ∩ G.vertexSet W ⊆ {s} := by
    rw [liftRealFamily_vertexSet]
    exact hTX
  obtain ⟨U, hU, hUV, hUI, hUT, hpsEdges, htrace⟩ :=
    ColouredSafeOnePortSplice.exists_onePortSplice_with_path hW.isWarp
      (liftRealFamily_isWarp T.isWarp) (liftRealFamily_finiteCharacter T.finiteCharacter)
      hsTerminal ps hpsK hps hKinter
  rw [liftRealFamily_vertexSet] at hUV
  rw [liftRealFamily_initialSet, T.initials_sdiff_source hs] at hUI
  rw [liftRealFamily_terminalFrontier, T.terminals] at hUT
  have hcover : CoversSource U (C.ladder.frontier a) := by
    apply coversSource_of_newlyTouched hW.covers_source
    · rw [hUI]
      exact Set.subset_union_left
    · intro p hp hpFrontier hpOld hpNew
      obtain ⟨x, hxp, hxU⟩ := hpNew
      rw [hUV] at hxU
      rcases hxU with hxW | hxT
      · exact False.elim (hpOld ⟨x, hxp, hxW⟩)
      · rw [hUI]
        exact Or.inr (T.limitOwner_initial_mem_touchedReference_of_meets
          C.legal hARoof hTRoof hp hpFrontier ⟨x, hxp, hxT⟩)
  have hTClosed : Gamma.vertexSet T.paths ⊆ Z :=
    T.carrier_subset.trans
      ((A.retypeStageReference_referenceClosure_subset C.legal hARoof).trans
        (A.referenceClosure_subset_of_closedUnderPaths hZ (hclosed A hA.2.2.2.2)))
  have hUcard : #(G.vertexSet U) ≤ kappa := by
    rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le
      C.capacity_infinite hWcard (T.carrier_countable.le_aleph0.trans C.capacity_infinite))
  have hnewTerminals : Gamma.terminalFrontier
      (A.retypeStageReference C.legal hARoof).touchedReference ⊆ C.ladder.frontier a := by
    rintro x ⟨p, hp, hpx⟩
    rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpx⟩
  have hBlueprint : IsLinkageBlueprint U (C.ladder.frontier a) Z persistent := {
    isWarp := hU
    vertices_roofed := by
      rw [hUV]
      exact Set.union_subset hW.vertices_roofed hTRoof
    covers_source := hcover
    vertices_closed := by
      rw [hUV]
      exact Set.union_subset hW.vertices_closed hTClosed
    card_paths := (mk_paths_le_vertexSet hU).trans hUcard
    infinitely_many_strong := DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace
      hW.infinitely_many_strong htrace
    terminals_popular := by
      rw [hUT]
      exact Set.union_subset (fun _ hx ↦ hW.terminals_popular hx.1)
        (hnewTerminals.trans Set.subset_union_right) }
  have hpE : ps.edgeSet = T.sourcePath.edgeSet :=
    LinkageBlueprint.walk_edgeSet_lift _ T.sourcePath.walk
  refine ⟨T.sourcePath, U, T.source_start, hfinish, hpE ▸ hpsEdges, ?_,
    hBlueprint, ?_, ?_, ?_⟩
  · rw [hUV]
    intro x hx
    exact Or.inr ⟨.inl T.sourcePath, T.source_mem, hx⟩
  · rw [hUI]
    exact Set.subset_union_left
  · rw [hUV]
    exact Set.subset_union_left
  · rw [hUT]
    exact Set.union_subset Set.subset_union_left (hnewTerminals.trans Set.subset_union_right)

#print axioms exists_infiniteBlueprintTransaction

end Erdos599.Blueprint.ColouredSafeShortcutGraph
