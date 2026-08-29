/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointSwitchSourceCoverage
import ErdosProblems.Erdos599.ColouredSafeEndpointPortSplices
import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability

/-!
# Actual source-covered strong and infinite endpoint-pruned replacements

Select the full protected switch and insert all of its actual members.
Exact edge, carrier and boundary equations retain full-reference source
coverage, the small roofed carrier, frontier terminal legality and arbitrary
fixed marked rays. Each real source component reaches the displayed frontier.
Uniform fixed-stage capture remains an explicit hypothesis, not a consequence
silently inferred from an existential captured-stage filter.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma D : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_strong_exists_sourceCovered_splice
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {W : Set D.DPath} (hW : D.IsWarp W) (hWcard : #(D.vertexSet W) ≤ kappa)
    (hWRoof : D.vertexSet W ⊆ Gamma.roof (C.ladder.frontier a))
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp (D.vertexSet W)))
    {marked : V → V → Prop} (hmarked : D.InfinitelyManyMarkedEdges W marked)
    {s t : V} (hedge : (s, t) ∈ familyEdges W) (hne : s ≠ t)
    {extra : Occurrence (reference C.ladder.limitWarp s (some t)) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s (some t)) s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a)) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s (some t)) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedStrongSwitch (A.retypeEndpointStageReference C.legal hARoof) t,
          ∃ U : Set D.DPath, D.IsWarp U ∧
            familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges T.paths ∧
            D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet T.paths ∧
            D.initialSet U = D.initialSet W ∪ (Gamma.initialSet T.paths \ {s}) ∧
            D.terminalFrontier U =
              D.terminalFrontier W ∪ (Gamma.terminalFrontier T.paths \ {t}) ∧
            T.sourcePath.edgeSet ⊆ familyEdges U ∧
            T.sourcePath.finish ∈ C.ladder.frontier a ∧
            #(D.vertexSet U) ≤ kappa ∧
            D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) ∧
            D.InfinitelyManyMarkedEdges U marked ∧
            D.terminalFrontier U ⊆ D.terminalFrontier W ∪ C.ladder.frontier a ∧
            Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
              (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
                referencePathsMeeting C.ladder.limitWarp (D.vertexSet U)) := by
  obtain ⟨A, hA, hARoof, T, hTX, _hSourceX, _hTerminalX, _hCompX,
      hTRoof, hEss, hfinish⟩ :=
    C.endpoint_hasCard_exists_strongTouchedSwitch_avoiding ha hne h hroof hWcard
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, hpE, htrace⟩ :=
    T.exists_spliceIn_exact hAdj hW hedge hTX
  have hUcard : #(D.vertexSet U) ≤ kappa := by
    rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      hWcard (T.carrier_countable.le_aleph0.trans C.capacity_infinite))
  have hURoof : D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) := by
    rw [hUV]
    exact Set.union_subset hWRoof hTRoof
  have hends : endpoints s (some t) ⊆ D.vertexSet W := by
    rw [endpoints_some, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact familyEdges_subset_vertexSet_prod W hedge
  have hsource := ColouredSafeEndpointSourceCoverage.sourceCondition_of_endpointSwitch_initials_eq
    C.legal A hARoof hTRoof T.carrier_subset T.initials hends hcover hUI hUV
  have hterm : D.terminalFrontier U ⊆ D.terminalFrontier W ∪ C.ladder.frontier a := by
    rw [hUT]
    rintro x (hxOld | ⟨hxNew, hxNot⟩)
    · exact Or.inl hxOld
    · rw [T.terminals] at hxNew
      rcases hxNew with hxRef | hxt
      · right
        obtain ⟨p, hp, hpx⟩ := hxRef
        rw [← ladderReference.terminalFrontier_eq C.legal]
        exact ⟨p, hEss hp, hpx⟩
      · exact False.elim (hxNot hxt)
  exact ⟨A, hA, hARoof, T, U, hU, hUE, hUV, hUI, hUT, hpE, hfinish, hUcard, hURoof,
    DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace hmarked htrace, hterm, hsource⟩

theorem endpoint_infinite_exists_sourceCovered_splice
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {W : Set D.DPath} (hW : D.IsWarp W) (hWcard : #(D.vertexSet W) ≤ kappa)
    (hWRoof : D.vertexSet W ⊆ Gamma.roof (C.ladder.frontier a))
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp (D.vertexSet W)))
    {marked : V → V → Prop} (hmarked : D.InfinitelyManyMarkedEdges W marked)
    {s : V} (hsTerminal : s ∈ D.terminalFrontier W)
    {extra : Occurrence (reference C.ladder.limitWarp s none) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s none) s none extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a)) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s none) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s none) s none extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedInfiniteSwitch (A.retypeEndpointStageReference C.legal hARoof),
          ∃ U : Set D.DPath, D.IsWarp U ∧
            familyEdges U = familyEdges W ∪ familyEdges T.paths ∧
            D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet T.paths ∧
            D.initialSet U = D.initialSet W ∪ (Gamma.initialSet T.paths \ {s}) ∧
            D.terminalFrontier U = (D.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier T.paths ∧
            T.sourcePath.edgeSet ⊆ familyEdges U ∧
            T.sourcePath.finish ∈ C.ladder.frontier a ∧
            #(D.vertexSet U) ≤ kappa ∧
            D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) ∧
            D.InfinitelyManyMarkedEdges U marked ∧
            D.terminalFrontier U ⊆ (D.terminalFrontier W \ {s}) ∪ C.ladder.frontier a ∧
            Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
              (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
                referencePathsMeeting C.ladder.limitWarp (D.vertexSet U)) := by
  obtain ⟨A, hA, hARoof, T, hTX, _hCompX, hTRoof, hEss, hfinish⟩ :=
    C.endpoint_hasCard_exists_infiniteTouchedSwitch_avoiding ha h hroof hWcard
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, hpE, htrace⟩ :=
    T.exists_spliceIn_exact hAdj hW hsTerminal hTX
  have hUcard : #(D.vertexSet U) ≤ kappa := by
    rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      hWcard (T.carrier_countable.le_aleph0.trans C.capacity_infinite))
  have hURoof : D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) := by
    rw [hUV]
    exact Set.union_subset hWRoof hTRoof
  have hends : endpoints s none ⊆ D.vertexSet W := by
    rw [endpoints_none, Set.singleton_subset_iff]
    obtain ⟨p, hp, hps⟩ := hsTerminal
    exact ⟨p, hp, D.terminal_mem_support hps⟩
  have hsource := ColouredSafeEndpointSourceCoverage.sourceCondition_of_endpointSwitch_initials_eq
    C.legal A hARoof hTRoof T.carrier_subset T.initials hends hcover hUI hUV
  have hterm : D.terminalFrontier U ⊆ (D.terminalFrontier W \ {s}) ∪ C.ladder.frontier a := by
    rw [hUT, T.terminals]
    apply Set.union_subset Set.subset_union_left
    rintro x ⟨p, hp, hpx⟩
    right
    rw [← ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpx⟩
  exact ⟨A, hA, hARoof, T, U, hU, hUE, hUV, hUI, hUT, hpE, hfinish, hUcard, hURoof,
    DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace hmarked htrace, hterm, hsource⟩

#print axioms endpoint_strong_exists_sourceCovered_splice
#print axioms endpoint_infinite_exists_sourceCovered_splice

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
