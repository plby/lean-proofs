/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStrongSourceCoverage
import ErdosProblems.Erdos599.ColouredSafeStrongTwoPortSplice

/-!
# Actual finite-end native strong blueprint transaction

Select the complete protected nondegenerate switch, lift its real paths,
and perform the graph-independent two-port insertion. The resulting actual
warp preserves all six native blueprint conditions and contains a real
path from the chosen edge tail into the displayed frontier. Uniform roof
and closing-set filters remain explicit; no fair limit is inferred.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

theorem exists_strongBlueprintTransaction
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s t : V} (hne : s ≠ t) (hedge : (s, t) ∈ familyEdges W)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
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
        (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∪ C.ladder.frontier a := by
  let G := imaginaryWeb C.ladder.limitWarp kappa
  have hWcard : #(G.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  obtain ⟨A, hA, hARoof, T, hTX, _hsourceX, _hterminalX, _hcompX, hTRoof, hEss, hfinish⟩ :=
    C.native_global_hasCard_exists_strongTouchedSwitch_avoiding ha hne h hroof hWcard
  have hstageV : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2, E.support_subset ⟨p, hp⟩ hxp⟩
  have hs : s ∉ Gamma.vertexSet (C.ladder.warpAt a) :=
    fun hv ↦ hA.2.2.1 (hstageV hv)
  have ht : t ∉ Gamma.vertexSet (C.ladder.warpAt a) :=
    fun hv ↦ hA.2.2.2.1 t rfl (hstageV hv)
  let K : Set G.DPath := liftRealFamily T.paths
  let ps : FinitePath G.graph := T.sourcePath.lift (fun he ↦ Or.inl he)
  let qt : FinitePath G.graph := T.terminalPath.lift (fun he ↦ Or.inl he)
  have hpV : ps.support = T.sourcePath.support := FinitePath.support_lift _ _
  have hqV : qt.support = T.terminalPath.support := FinitePath.support_lift _ _
  have hdistinct : (Sum.inl ps : G.DPath) ≠ Sum.inl qt := by
    intro he
    have heq : ps = qt := Sum.inl.inj he
    have hv : T.sourcePath.support = T.terminalPath.support :=
      hpV.symm.trans ((congrArg FinitePath.support heq).trans hqV)
    exact Set.disjoint_left.mp T.port_supports_disjoint T.sourcePath.start_mem_support
      (hv ▸ T.sourcePath.start_mem_support)
  obtain ⟨old, hOld, hOldEdge⟩ :=
    Set.mem_iUnion.mp hedge |>.imp fun _ h ↦ Set.mem_iUnion.mp h
  let S : ColouredSafeStrongTwoPortSplice.Data W K s t := {
    old := old
    old_mem := hOld
    old_edge := hOldEdge
    W_isWarp := hW.isWarp
    switch_isWarp := liftRealFamily_isWarp T.isWarp
    switch_finiteCharacter := liftRealFamily_finiteCharacter T.finiteCharacter
    fromTail := ps
    toHead := qt
    fromTail_mem := ⟨.inl T.sourcePath, T.source_mem, rfl⟩
    toHead_mem := ⟨.inl T.terminalPath, T.terminal_mem, rfl⟩
    fromTail_ne_toHead := hdistinct
    fromTail_start := T.source_start
    toHead_finish := T.terminal_finish
    carrier_inter := by
      change (imaginaryWeb C.ladder.limitWarp kappa).vertexSet (liftRealFamily T.paths) ∩
        G.vertexSet W ⊆ {s, t}
      rw [liftRealFamily_vertexSet]
      exact hTX }
  have hUI : G.initialSet S.paths = G.initialSet W ∪ (Gamma.initialSet T.paths \ {s}) := by
    rw [S.initialSet_paths]
    change G.initialSet W ∪
      ((imaginaryWeb C.ladder.limitWarp kappa).initialSet (liftRealFamily T.paths) \ {s}) = _
    rw [liftRealFamily_initialSet]
  have hUT : G.terminalFrontier S.paths =
      G.terminalFrontier W ∪ (Gamma.terminalFrontier T.paths \ {t}) := by
    rw [S.terminalFrontier_paths]
    change G.terminalFrontier W ∪
      ((imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier (liftRealFamily T.paths) \ {t}) = _
    rw [liftRealFamily_terminalFrontier]
  have hUV : G.vertexSet S.paths = G.vertexSet W ∪ Gamma.vertexSet T.paths := by
    rw [S.vertexSet_paths]
    change G.vertexSet W ∪
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet (liftRealFamily T.paths) = _
    rw [liftRealFamily_vertexSet]
  have hBlueprint := isLinkageBlueprint_of_stageStrongSwitch C hZ hW hARoof T hs ht
    hTRoof (hclosed A hA.2.2.2.2) hEss S.paths_isWarp hUI hUT hUV S.finite_rayTrace
  have hSourceEdges : T.sourcePath.edgeSet ⊆ familyEdges S.paths := by
    intro e he
    have hpE : ps.edgeSet = T.sourcePath.edgeSet :=
      LinkageBlueprint.walk_edgeSet_lift _ T.sourcePath.walk
    have hleftE : S.left.edgeSet = S.split.front.edgeSet ∪ S.fromTail.edgeSet :=
      LinkageBlueprint.FinitePath.edgeSet_appendFinite _ _ _ _
    have heLeft : e ∈ S.left.edgeSet := by
      rw [hleftE]
      exact Or.inr (hpE.symm ▸ he)
    exact Set.mem_iUnion.mpr ⟨.inl S.left, Set.mem_iUnion.mpr ⟨S.left_mem_paths, heLeft⟩⟩
  refine ⟨T.sourcePath, S.paths, T.source_start, hfinish, hSourceEdges, ?_,
    hBlueprint, ?_, ?_, ?_⟩
  · rw [hUV]
    intro x hx
    exact Or.inr ⟨.inl T.sourcePath, T.source_mem, hx⟩
  · rw [hUI]
    exact Set.subset_union_left
  · rw [hUV]
    exact Set.subset_union_left
  · rw [hUT, T.terminals_sdiff_end ht]
    apply Set.union_subset Set.subset_union_left
    rintro x ⟨p, hp, hpx⟩
    right
    rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpx⟩

#print axioms exists_strongBlueprintTransaction

end Erdos599.Blueprint.ColouredSafeShortcutGraph
