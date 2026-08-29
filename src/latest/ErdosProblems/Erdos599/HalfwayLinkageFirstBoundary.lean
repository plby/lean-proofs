/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutConstruction
import ErdosProblems.Erdos599.WarpFamilyBoundary

/-!
# Boundary of a linkage-first closed cut

If the closing operation is performed after the later finite-character warp
has been selected, and is closed under that warp, then the ``outside cut''
does not split any member of the warp.  Its roots and sinks are therefore
exactly the original roots and finite terminals which lie outside the closed
set.  This file proves that reduction directly from the literal definitions
of `outsideCarrier`, `outsideFamilyEdges`, and `CutSplit`.

The final constructor records the sharp remaining obligations for
`OutsideCutBoundary`: ordinary compatibility of the later row with the
reference row, exclusion of the reference initials from the closing set, and
the two club-stage location inclusions.  In particular none of the five cut
boundary fields is assumed as an undischarged package.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y W : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}

/-! ## Roots and sinks of an arbitrary warp -/

/-- For a warp, the path-family initials are precisely its carrier vertices
without an incoming family edge. -/
theorem isWarp_initialSet_eq_noIncoming (hW : Gamma.IsWarp W) :
    Gamma.initialSet W =
      {x | x ∈ Gamma.vertexSet W ∧ ¬ ∃ y, (y, x) ∈ familyEdges W} := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hpW, hpinitial⟩ := hx
    exact ⟨⟨p, hpW, hpinitial.symm ▸ p.initial_mem_support⟩,
      isWarp_noIncoming_familyEdges_of_mem_initialSet hW
        ⟨p, hpW, hpinitial⟩⟩
  · rintro ⟨⟨p, hpW, hxp⟩, hno⟩
    refine ⟨p, hpW, ?_⟩
    by_contra hpinitial
    have hne : x ≠ p.initial := by
      intro h
      exact hpinitial h.symm
    rcases p with p | r
    · obtain ⟨y, hyx⟩ :=
        FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p hxp hne
      exact hno ⟨y, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
        Set.mem_iUnion.2 ⟨hpW, hyx⟩⟩⟩
    · obtain ⟨n, hn⟩ := hxp
      cases n with
      | zero => exact hne (by simpa [Path.initial, Ray.initial] using hn.symm)
      | succ n =>
          exact hno ⟨r n, Set.mem_iUnion.2 ⟨(Sum.inr r : Gamma.DPath),
            Set.mem_iUnion.2 ⟨hpW, ⟨n, by
              exact Prod.ext rfl hn.symm⟩⟩⟩⟩

/-- For a warp, the finite terminal frontier is precisely its carrier
vertices without an outgoing family edge.  A ray carrier vertex always has
a successor, so it cannot occur on the right-hand side. -/
theorem isWarp_terminalFrontier_eq_noOutgoing (hW : Gamma.IsWarp W) :
    Gamma.terminalFrontier W =
      {x | x ∈ Gamma.vertexSet W ∧ ¬ ∃ y, (x, y) ∈ familyEdges W} := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨hx.choose, hx.choose_spec.1,
        Gamma.terminal_mem_support hx.choose_spec.2⟩,
      isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier hW hx⟩
  · rintro ⟨⟨p, hpW, hxp⟩, hno⟩
    rcases p with p | r
    · have hfinish : x = p.finish := by
        by_contra hne
        obtain ⟨y, hxy⟩ :=
          FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            p hxp hne
        exact hno ⟨y, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
          Set.mem_iUnion.2 ⟨hpW, hxy⟩⟩⟩
      refine ⟨Sum.inl p, hpW, ?_⟩
      simp [DWeb.terminal?, Path.terminal?, hfinish]
    · obtain ⟨n, rfl⟩ := hxp
      exact False.elim <| hno ⟨r (n + 1),
        Set.mem_iUnion.2 ⟨(Sum.inr r : Gamma.DPath),
          Set.mem_iUnion.2 ⟨hpW, ⟨n, rfl⟩⟩⟩⟩

/-! ## A row-closed cut does not split the row -/

/-- Every literal cut initial lies in the outside carrier. -/
theorem cutInitial_subset_outsideCarrier :
    CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X ⊆ outsideCarrier W X := by
  intro x hx
  rcases hx with hx | hx
  · exact (outsideFamilyEdges_endpoints W X hx.2.choose_spec).1
  · exact hx.1

/-- Every literal cut terminal lies in the outside carrier. -/
theorem cutTerminal_subset_outsideCarrier :
    CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X ⊆ outsideCarrier W X := by
  intro x hx
  rcases hx with hx | hx
  · exact (outsideFamilyEdges_endpoints W X hx.2.choose_spec).2
  · exact hx.1

/-- Once `X` is closed under every member of `W`, the literal outside-cut
roots are exactly the original warp initials outside `X`. -/
theorem cutInitial_eq_initialSet_sdiff_of_closedUnderPaths
    (hW : Gamma.IsWarp W) (hclosed : ClosedUnderPaths Gamma W X) :
    CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X = Gamma.initialSet W \ X := by
  have hdisjoint : Disjoint (outsideCarrier W X) X :=
    outsideCarrier_disjoint_of_closedUnderPaths W X hclosed
  rw [isWarp_initialSet_eq_noIncoming hW]
  ext x
  constructor
  · intro hx
    have hxCarrier := cutInitial_subset_outsideCarrier (W := W) (X := X) hx
    have hxNotX : x ∉ X := Set.disjoint_left.1 hdisjoint hxCarrier
    have hxVertex : x ∈ Gamma.vertexSet W := by
      rcases hxCarrier with hxOutside | hxIncident
      · exact hxOutside.1
      · obtain ⟨y, hxy | hyx⟩ := hxIncident
        · exact (familyEdges_subset_vertexSet_prod W hxy.1).1
        · exact (familyEdges_subset_vertexSet_prod W hyx.1).2
    refine ⟨⟨hxVertex, ?_⟩, hxNotX⟩
    rintro ⟨y, hyx⟩
    rcases hx with hxCut | hxOutside
    · exact hxNotX hxCut.1
    · apply hxOutside.2.2
      exact ⟨y, hyx, fun hboth ↦ hxNotX hboth.2⟩
  · rintro ⟨⟨hxVertex, hnoIncoming⟩, hxNotX⟩
    exact Or.inr ⟨Or.inl ⟨hxVertex, hxNotX⟩, hxNotX, fun hin ↦
      hnoIncoming ⟨hin.choose, hin.choose_spec.1⟩⟩

/-- Once `X` is closed under every member of `W`, the literal outside-cut
sinks are exactly the original finite terminals outside `X`. -/
theorem cutTerminal_eq_terminalFrontier_sdiff_of_closedUnderPaths
    (hW : Gamma.IsWarp W) (hclosed : ClosedUnderPaths Gamma W X) :
    CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X = Gamma.terminalFrontier W \ X := by
  have hdisjoint : Disjoint (outsideCarrier W X) X :=
    outsideCarrier_disjoint_of_closedUnderPaths W X hclosed
  rw [isWarp_terminalFrontier_eq_noOutgoing hW]
  ext x
  constructor
  · intro hx
    have hxCarrier := cutTerminal_subset_outsideCarrier (W := W) (X := X) hx
    have hxNotX : x ∉ X := Set.disjoint_left.1 hdisjoint hxCarrier
    have hxVertex : x ∈ Gamma.vertexSet W := by
      rcases hxCarrier with hxOutside | hxIncident
      · exact hxOutside.1
      · obtain ⟨y, hxy | hyx⟩ := hxIncident
        · exact (familyEdges_subset_vertexSet_prod W hxy.1).1
        · exact (familyEdges_subset_vertexSet_prod W hyx.1).2
    refine ⟨⟨hxVertex, ?_⟩, hxNotX⟩
    rintro ⟨y, hxy⟩
    rcases hx with hxCut | hxOutside
    · exact hxNotX hxCut.1
    · apply hxOutside.2.2
      exact ⟨y, hxy, fun hboth ↦ hxNotX hboth.1⟩
  · rintro ⟨⟨hxVertex, hnoOutgoing⟩, hxNotX⟩
    exact Or.inr ⟨Or.inl ⟨hxVertex, hxNotX⟩, hxNotX, fun hout ↦
      hnoOutgoing ⟨hout.choose, hout.choose_spec.1⟩⟩

/-! ## Sharp boundary constructor -/

/-- Construct the five literal cut-boundary fields from row-level geometry.

The first two assumptions say that contacts of a later-row endpoint with the
reference carrier occur only at the corresponding reference endpoint.  The
third and fourth say that every reference initial is a later-row initial and
is not swallowed by the closing set.  The last two are the ordinary
club-stage location statements for non-reference endpoints. -/
theorem OutsideCutBoundary.of_closedUnderLater
    (hW : Gamma.IsWarp W) (hclosed : ClosedUnderPaths Gamma W X)
    (hinitial_on_reference :
      Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆ Gamma.initialSet Y)
    (hterminal_on_reference :
      Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
        Gamma.terminalFrontier Y)
    (hreference_initials : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hreference_away : Disjoint (Gamma.initialSet Y) X)
    (hsource_location :
      Gamma.initialSet W \ Gamma.initialSet Y ⊆ before ∩ innerRoof)
    (hterminal_location :
      Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
        before ∩ outerRoof) :
    OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof := by
  have hinitial := cutInitial_eq_initialSet_sdiff_of_closedUnderPaths
    (W := W) (X := X) hW hclosed
  have hterminal := cutTerminal_eq_terminalFrontier_sdiff_of_closedUnderPaths
    (W := W) (X := X) hW hclosed
  constructor
  · rw [hinitial]
    intro x hx
    exact hinitial_on_reference ⟨hx.1.1, hx.2⟩
  · rw [hterminal]
    intro x hx
    exact hterminal_on_reference ⟨hx.1.1, hx.2⟩
  · rw [hinitial]
    intro x hx
    exact ⟨hreference_initials hx,
      Set.disjoint_left.1 hreference_away hx⟩
  · rw [hinitial]
    intro x hx
    exact hsource_location ⟨hx.1.1, hx.2⟩
  · rw [hterminal]
    intro x hx
    exact hterminal_location ⟨hx.1.1, hx.2⟩

/-! ## Compatibility audit for linkage-first closure -/

/-- A boundary package for a cut which is closed under the later row forces
every reference initial to stay outside the closing set.  This necessary
condition is easy to miss because `reference_initials` itself only mentions
the cut-root relation. -/
theorem OutsideCutBoundary.referenceInitials_disjoint_of_closedUnderLater
    (B : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (hclosed : ClosedUnderPaths Gamma W X) :
    Disjoint (Gamma.initialSet Y) X := by
  have houtside : Disjoint (outsideCarrier W X) X :=
    outsideCarrier_disjoint_of_closedUnderPaths W X hclosed
  rw [Set.disjoint_left]
  intro x hxY hxX
  have hxCut := B.reference_initials hxY
  have hxCarrier :=
    cutInitial_subset_outsideCarrier (W := W) (X := X) hxCut
  exact Set.disjoint_left.1 houtside hxCarrier hxX

/-- If `X` is also closed under the reference row, the preceding necessary
condition propagates along every reference member: the whole reference
carrier must be disjoint from `X`.  Thus a linkage-first seed whose natural
initial set already contains a reference vertex cannot possibly satisfy the
current `OutsideCutBoundary` interface. -/
theorem OutsideCutBoundary.referenceVertexSet_disjoint_of_closedRows
    (B : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (hlater : ClosedUnderPaths Gamma W X)
    (hreference : ClosedUnderPaths Gamma Y X) :
    Disjoint (Gamma.vertexSet Y) X := by
  have hinitial := B.referenceInitials_disjoint_of_closedUnderLater hlater
  rw [Set.disjoint_left]
  rintro x ⟨p, hpY, hxp⟩ hxX
  have hpX : p.support ⊆ X := hreference p hpY ⟨x, hxp, hxX⟩
  have hpInitialX := hpX p.initial_mem_support
  have hpInitialY : p.initial ∈ Gamma.initialSet Y := ⟨p, hpY, rfl⟩
  exact Set.disjoint_left.1 hinitial hpInitialY hpInitialX

/-- Concrete obstruction for a proposed linkage-first seed: if its mandatory
initial seed meets the reference carrier, simultaneous closure under the
later and reference rows is incompatible with `OutsideCutBoundary`. -/
theorem no_outsideCutBoundary_of_seed_meets_reference
    {initialSeed : Set V}
    (hseed : initialSeed ⊆ X)
    (hmeet : (initialSeed ∩ Gamma.vertexSet Y).Nonempty)
    (hlater : ClosedUnderPaths Gamma W X)
    (hreference : ClosedUnderPaths Gamma Y X) :
    ¬ OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof := by
  intro B
  obtain ⟨x, hxSeed, hxY⟩ := hmeet
  exact Set.disjoint_left.1
    (B.referenceVertexSet_disjoint_of_closedRows hlater hreference)
    hxY (hseed hxSeed)

end LinkageBlueprint
end Blueprint
end Erdos599
