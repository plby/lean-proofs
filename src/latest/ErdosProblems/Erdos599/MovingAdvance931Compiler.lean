/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.MovingAdvance931

/-!
# Relation compilation for moving-slice Assertion 9.31

The relation constructed by Assertion 9.31 is roofed and stable at the new
slice.  Its scheduled endpoint, however, belongs to the old slice reached by
Assertion 9.30.  This file keeps those two roles separate while compiling the
relation to a blueprint.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Compile a new-slice splice relation while retaining the old slice in
the terminal-exception clause of Assertion 9.31. -/
theorem AdvanceSpliceRelation.exists_predecessorPreservingMovingAdvance931_with_edgeSet
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z persistent B : Set V}
    (S : AdvanceSpliceRelation
      ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewRealPredecessorsTo U ∧ U.edgeSet = S.edge := by
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    S.edge S.carrier S.edge_in_graph S.endpoints_mem S.biunique
      S.no_directed_cycle S.no_reverse_ray
  have hsink_terminal :
      {x | x ∈ S.carrier ∧ ¬ ∃ y, (x, y) ∈ S.edge} =
        (orientationBlueprint O).terminalSet := by
    rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
  have hreal_sink_terminal :
      relationRealTerminals (Gamma := Gamma) S.edge S.carrier =
        (orientationBlueprint O).realPart.terminals := by
    simp only [FamilyGraph.terminals, FamilyGraph.tails, realPart_vertices,
      realPart_edges, orientationBlueprint_vertexSet,
      orientationBlueprint_edgeSet, hOC, hOE, relationRealTerminals,
      relationRealEdges]
  have hpopular : (orientationBlueprint O).terminalSet ⊆
      {x | IsPopular Gamma Y persistent kappa x} ∪ Tnew := by
    rw [← hsink_terminal]
    exact S.sink_boundary
  have hcard : #(orientationBlueprint O).paths ≤ kappa := by
    change #(Set.range O.rootPath) ≤ kappa
    refine Cardinal.mk_range_le.trans ?_
    refine (Cardinal.mk_subtype_mono (fun x hx ↦ hx.1)).trans ?_
    simpa only [hOC] using S.card_carrier
  have hstrong : (orientationBlueprint O).InfinitelyManyStrongEdges := by
    intro r hr
    apply S.every_relation_ray_strong r
    intro e he
    rw [← hOE, ← orientationBlueprint_edgeSet O]
    exact Set.mem_iUnion.2 ⟨(Sum.inr r :
      DirectedPath.Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hr, he⟩⟩
  have hrealTerminals : current.realPart.terminals ⊆
      (orientationBlueprint O).realPart.terminals ∪ Told := by
    intro x hx
    by_cases hxz : x = z
    · exact Or.inr (hxz ▸ hzOld)
    · exact Or.inl <| hreal_sink_terminal ▸
        S.preserves_other_real_terminals ⟨hx, hxz⟩
  have hpersistent : current.terminalSet ∩ persistent ⊆
      (orientationBlueprint O).terminalSet ∪ {z} := by
    rw [← hsink_terminal]
    exact S.persistent_boundary
  have hpreserves : current.realPart.terminals \ {z} ⊆
      (orientationBlueprint O).realPart.terminals := by
    rw [← hreal_sink_terminal]
    exact S.preserves_other_real_terminals
  have hinherited : ∀ x, x ∈ ancestor.terminalSet →
      x ∈ current.terminalSet → x ≠ z →
        x ∈ (orientationBlueprint O).terminalSet := by
    intro x hxA hxcurrent hxz
    rw [← hsink_terminal]
    exact S.inherited_boundary x hxA hxcurrent hxz
  let U := orientationBlueprint O
  have hUblueprint : U.IsLinkageBlueprint Tnew Z persistent := by
    refine {
      vertices_roofed := ?_
      covers_source := ?_
      vertices_closed := ?_
      card_paths := hcard
      infinitely_many_strong := hstrong
      terminals_popular := hpopular }
    · simpa only [U, orientationBlueprint_vertexSet, hOC] using
        S.vertices_roofed
    · simpa only [U, orientationBlueprint_initialSet_eq_no_incoming,
        retainedReferenceInitials, orientationBlueprint_vertexSet,
        hOC, hOE] using S.covers_source
    · simpa only [U, orientationBlueprint_vertexSet, hOC] using
        S.vertices_closed
  have hstable : U.Stable Tnew persistent := by
    change (orientationBlueprint O).terminalSet ∩ Tnew ⊆ persistent
    rw [← hsink_terminal]
    exact S.stable_boundary
  have hordinary : current.OrdinaryExtends U := by
    constructor
    · simpa only [familyGraph, U, orientationBlueprint_vertexSet, hOC]
        using S.old_vertices
    · simpa only [familyGraph, U, orientationBlueprint_edgeSet, hOE]
        using S.old_edges
  have hlinks : U.RealLinksTo z B := by
    refine ⟨S.target_path, S.target_path_start, S.target_path_finish, ?_, ?_⟩
    · simpa only [U, realPart_vertices, orientationBlueprint_vertexSet, hOC]
        using S.target_path_vertices
    · simpa only [U, realPart_edges, orientationBlueprint_edgeSet, hOE,
        relationRealEdges] using S.target_path_edges
  have hadvance :
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B := by
    exact {
      conclusion := ⟨hordinary, hlinks, hrealTerminals, hpersistent⟩
      isBlueprint := hUblueprint
      stable := hstable
      family_extends := hordinary
      real_extends := hordinary.realPart_extends
      preserves_except := hpreserves
      preserves_inherited_full_terminals := hinherited }
  have hnoNew : current.NoNewRealPredecessorsTo U := by
    intro x y hx hnew
    apply S.no_new_real_predecessors hx
    simpa only [U, realPart_edges, orientationBlueprint_edgeSet, hOE,
      relationRealEdges] using hnew
  refine ⟨U, hadvance, hnoNew, ?_⟩
  simpa only [U, orientationBlueprint_edgeSet] using hOE

/-- Forget the exact edge-set identity after moving-slice compilation. -/
theorem AdvanceSpliceRelation.exists_predecessorPreservingMovingAdvance931
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z persistent B : Set V}
    (S : AdvanceSpliceRelation
      ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewRealPredecessorsTo U := by
  obtain ⟨U, hU, hnoNew, _⟩ :=
    S.exists_predecessorPreservingMovingAdvance931_with_edgeSet hzOld
  exact ⟨U, hU, hnoNew⟩

/-- Fresh attachment geometry retains full predecessor preservation while
the result moves to a later slice. -/
theorem FreshAdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z persistent B : Set V}
    (S : FreshAdvanceSpliceRelation
      ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewPredecessorsTo U := by
  let R := S.toAdvanceSpliceRelation
  obtain ⟨U, hU, _hnoReal, hedge⟩ :=
    R.exists_predecessorPreservingMovingAdvance931_with_edgeSet hzOld
  refine ⟨U, hU, ?_⟩
  intro x y hx hxy
  have hxy' : (y, x) ∈ current.edgeSet ∪ S.fresh := by
    rw [hedge] at hxy
    exact hxy
  rcases hxy' with hxyOld | hxyFresh
  · exact hxyOld
  · exact False.elim (S.fresh_no_incoming_old_real
      (by simpa only [realPart_vertices] using hx) hxyFresh)

/-- Solve one concrete occurrence-aware request without identifying the old
scheduled slice with the new roof slice. -/
theorem OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest.exists_fullyPredecessorPreservingMovingAdvance931
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z persistent B : Set V}
    (R : OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewPredecessorsTo U := by
  obtain ⟨L, hL⟩ := CardinalInduction.isLinkable_of_source_mk_le_current
    hlower hext R.auxiliary R.auxiliary_unhindered R.source_card
  exact (R.compile L hL).some.1.attachment
    |>.exists_fullyPredecessorPreservingMovingAdvance931 hzOld

/-- Conditional compatibility interface for a relation compiler whose input
and output slices (and closure sets) are genuinely stage-indexed. -/
def MovingAdvanceSpliceRelationCompiler
    (Told Tnew Zold Znew persistent B : Set V) : Prop :=
  ∀ (W cut current : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint Told Zold persistent →
      Continuation930 W cut current u z Told B →
        Nonempty (AdvanceSpliceRelation
          W current z Tnew Znew persistent B)

/-- Result interface obtained from a moving relation compiler. -/
def PredecessorPreservingMovingAdvance931Compiler
    (Told Tnew Zold Znew persistent B : Set V) : Prop :=
  ∀ (W cut current : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint Told Zold persistent →
      Continuation930 W cut current u z Told B →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          MovingAdvance931 W current U z Told Tnew Znew persistent B ∧
            current.NoNewRealPredecessorsTo U

/-- Compile the minimal relation interface without identifying the old and
new slice indices. -/
theorem predecessorPreservingMovingAdvance931Compiler_of_relation
    {Told Tnew Zold Znew persistent B : Set V}
    (hrelation : MovingAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      Told Tnew Zold Znew persistent B) :
    PredecessorPreservingMovingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      Told Tnew Zold Znew persistent B := by
  intro W cut current u z hW hcontinuation
  exact (hrelation W cut current u z hW hcontinuation).some
    |>.exists_predecessorPreservingMovingAdvance931
      hcontinuation.endpoint_mem_slice

/-- One concrete occurrence-aware transition from an old slice to a new
slice.  This is the reachable-state seam; it does not quantify over
arbitrary blueprints. -/
structure OccurrenceCertifiedMoving934Transition
    (W : LinkageBlueprint Gamma Y kappa)
    (u : V) (Told Tnew Znew persistent B : Set V) where
  cut : LinkageBlueprint Gamma Y kappa
  current : LinkageBlueprint Gamma Y kappa
  endpoint : V
  continuation : Continuation930 W cut current u endpoint Told B
  request : OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
    W current endpoint Tnew Znew persistent B

/-- Compile one concrete moving occurrence transaction.  The caller supplies
the honest refinement certificate produced by its 9.30 geometry; the fresh
9.31 attachment supplies full predecessor preservation for the second leg. -/
theorem OccurrenceCertifiedMoving934Transition.compile
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {W : LinkageBlueprint Gamma Y kappa}
    {u : V} {Told Tnew Znew persistent B : Set V}
    (C : OccurrenceCertifiedMoving934Transition
      W u Told Tnew Znew persistent B)
    (h30refines : W.PredecessorRefines C.current) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      StableExtensionConclusion W U u Tnew Znew persistent B ∧
        W.PredecessorRefines U := by
  obtain ⟨U, h31, h31full⟩ :=
    C.request.exists_fullyPredecessorPreservingMovingAdvance931
      hlower hext C.continuation.endpoint_mem_slice
  exact ⟨U, movingAssertion934_of_refining_930_931
    C.continuation h31 h30refines h31full.predecessorRefines⟩

#print axioms
  AdvanceSpliceRelation.exists_predecessorPreservingMovingAdvance931_with_edgeSet
#print axioms
  FreshAdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931
#print axioms OccurrenceCertifiedMoving934Transition.compile

end Erdos599.Blueprint.LinkageBlueprint

