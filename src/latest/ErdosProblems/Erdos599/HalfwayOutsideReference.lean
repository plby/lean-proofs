/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint931
import ErdosProblems.Erdos599.OutsideReferenceCore
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary
import ErdosProblems.Erdos599.FracturedAssignmentPeel
import ErdosProblems.Erdos599.HalfwayFracturedAssignmentCompiler
import ErdosProblems.Erdos599.HalfwayCutFracturedProjection

/-!
# Removing the reference components swallowed by a closed cut

If `X` is closed under a reference warp `Y`, every member of `Y` is either
contained in `X` or disjoint from `X`.  The outside-fragment assignment in
Assertion 9.31 should therefore be made relative only to the second
subfamily.  This avoids the false requirement that initials of reference
members already swallowed by `X` remain initials of the outside cut.

This file proves the essential transfer theorem.  A safe alternating path
relative to the outside reference is safe relative to the full reference as
soon as its vertex set avoids `X`.  The omitted reference components cannot
meet the path, while their edge-interval clauses are empty.  Consequently
the ordinary Claim 2 applies with the original reference warp and the
original imaginary graph.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V}
variable {Y U : Set Gamma.DPath} {X : Set V}

theorem outsideReference_subset : outsideReference Y X ⊆ Y :=
  fun _ hp ↦ hp.1

theorem outsideReference_isWarp (hY : Gamma.IsWarp Y) :
    Gamma.IsWarp (outsideReference Y X) :=
  fun _ hp _ hq hpq ↦ hY hp.1 hq.1 hpq

theorem outsideReference_finiteCharacter
    (hY : Gamma.HasFiniteCharacter Y) :
    Gamma.HasFiniteCharacter (outsideReference Y X) :=
  fun hp ↦ hY hp.1

theorem vertexSet_outsideReference_subset :
    Gamma.vertexSet (outsideReference Y X) ⊆ Gamma.vertexSet Y := by
  rintro x ⟨p, hp, hxp⟩
  exact ⟨p, hp.1, hxp⟩

theorem initialSet_outsideReference_subset :
    Gamma.initialSet (outsideReference Y X) ⊆ Gamma.initialSet Y := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, hp.1, hpx⟩

/-- A full-reference initial which lies on an outside component is already
an initial of the pruned reference. -/
theorem initialSet_inter_vertexSet_outsideReference_subset
    (hY : Gamma.IsWarp Y) :
    Gamma.initialSet Y ∩ Gamma.vertexSet (outsideReference Y X) ⊆
      Gamma.initialSet (outsideReference Y X) := by
  rintro x ⟨⟨p, hpY, rfl⟩, q, hqout, hxp⟩
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hY hpY hqout.1
      p.initial_mem_support hxp
  subst q
  exact ⟨p, hqout, rfl⟩

/-- A full-reference terminal which lies on an outside component is already
a terminal of the pruned reference. -/
theorem terminalFrontier_inter_vertexSet_outsideReference_subset
    (hY : Gamma.IsWarp Y) :
    Gamma.terminalFrontier Y ∩
        Gamma.vertexSet (outsideReference Y X) ⊆
      Gamma.terminalFrontier (outsideReference Y X) := by
  rintro x ⟨hxterminal, q, hqout, hxq⟩
  exact ⟨q, hqout,
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      Gamma hY hqout.1 hxq hxterminal⟩

theorem familyEdges_outsideReference_subset :
    familyEdges (outsideReference Y X) ⊆ familyEdges Y := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, he⟩ := he
  exact ⟨p, hp.1, he⟩

/-- Reference closure gives the exact inside/outside dichotomy needed for
reference pruning. -/
theorem mem_outsideReference_or_support_subset
    (hclosed : ClosedUnderPaths Gamma Y X) {p : Gamma.DPath}
    (hpY : p ∈ Y) :
    p ∈ outsideReference Y X ∨ p.support ⊆ X := by
  by_cases hpX : Disjoint p.support X
  · exact Or.inl ⟨hpY, hpX⟩
  · exact Or.inr (hclosed p hpY
      (Set.not_disjoint_iff_nonempty_inter.mp hpX))

/-- Every omitted reference component is wholly swallowed by the closed
set. -/
theorem support_subset_of_mem_sdiff_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X) {p : Gamma.DPath}
    (hp : p ∈ Y \ outsideReference Y X) : p.support ⊆ X := by
  rcases mem_outsideReference_or_support_subset hclosed hp.1 with hpout | hpX
  · exact False.elim (hp.2 hpout)
  · exact hpX

/-- The outside reference carrier avoids the closed set definitionally. -/
theorem vertexSet_outsideReference_disjoint :
    Disjoint (Gamma.vertexSet (outsideReference Y X)) X := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hp, hxp⟩ hxX
  exact Set.disjoint_left.1 hp.2 hxp hxX

/-- Bracket provenance plus disjoint forward/reference owners makes the
whole alternating path avoid the cut.  The initial vertex is stated
separately so that trivial outside fragments are covered as well. -/
theorem disjoint_vertexSet_of_bracketSafe_outsideReference
    {Q : AltPath Gamma.graph}
    (hQ : IsBracketSafe U (outsideReference Y X) Q)
    (hinitial : Q.initial ∉ X)
    (hU : Disjoint (Gamma.vertexSet U) X) :
    Disjoint Q.vertexSet X := by
  rw [Set.disjoint_left]
  intro x hxQ hxX
  rcases Q.vertexSet_subset_initial_union_links hxQ with hxinitial | hxlink
  · have hxeq : x = Q.initial := by simpa using hxinitial
    exact hinitial (hxeq ▸ hxX)
  · simp only [Set.mem_iUnion] at hxlink
    obtain ⟨l, hlQ, hxl⟩ := hxlink
    cases hdirection : l.direction with
    | forward =>
        have hxU := (hQ.2.2 l hlQ hdirection).support_subset_vertexSet hxl
        exact Set.disjoint_left.1 hU hxU hxX
    | backward =>
        obtain ⟨p, hpout, hlp⟩ := hQ.1.1.2.1 l hlQ hdirection
        exact Set.disjoint_left.1 hpout.2 (hlp.1 hxl) hxX

/-- A path avoiding `X` cannot meet a full-reference component omitted by
`outsideReference`. -/
theorem disjoint_support_of_not_mem_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    {p : Gamma.DPath} (hpY : p ∈ Y)
    (hpout : p ∉ outsideReference Y X) :
    Disjoint Q.vertexSet p.support := by
  have hpX : p.support ⊆ X := by
    rcases mem_outsideReference_or_support_subset hclosed hpY with hp | hpX
    · exact False.elim (hpout hp)
    · exact hpX
  exact Set.disjoint_of_subset_right hpX hQX

namespace LinkageBlueprint

/-! ## Boundary transfer to the pruned reference -/

/-- The sharp row-level boundary constructor for the outside reference.

Unlike `OutsideCutBoundary.of_closedUnderLater`, this theorem does not ask
the initials of the full reference to avoid `X`.  Components swallowed by
the reference-closed set simply disappear from `outsideReference`; closure
under the later row identifies every literal cut endpoint with an original
later-row endpoint outside `X`. -/
theorem OutsideCutBoundary.of_closedUnderLater_outsideReference
    {W : Set Gamma.DPath} {before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hWclosed : ClosedUnderPaths Gamma W X)
    (hY : Gamma.IsWarp Y) (hYclosed : ClosedUnderPaths Gamma Y X)
    (hinitial_on_reference :
      Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆ Gamma.initialSet Y)
    (hterminal_on_reference :
      Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
        Gamma.terminalFrontier Y)
    (hreference_initials : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hsource_location :
      Gamma.initialSet W \ Gamma.initialSet Y ⊆ before ∩ innerRoof)
    (hterminal_location :
      Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
        before ∩ outerRoof) :
    OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof := by
  have hinitial := cutInitial_eq_initialSet_sdiff_of_closedUnderPaths
    (W := W) (X := X) hW hWclosed
  have hterminal := cutTerminal_eq_terminalFrontier_sdiff_of_closedUnderPaths
    (W := W) (X := X) hW hWclosed
  constructor
  · rw [hinitial]
    intro x hx
    apply initialSet_inter_vertexSet_outsideReference_subset hY
    exact ⟨hinitial_on_reference
      ⟨hx.1.1, vertexSet_outsideReference_subset hx.2⟩, hx.2⟩
  · rw [hterminal]
    intro x hx
    apply terminalFrontier_inter_vertexSet_outsideReference_subset hY
    exact ⟨hterminal_on_reference
      ⟨hx.1.1, vertexSet_outsideReference_subset hx.2⟩, hx.2⟩
  · rw [hinitial]
    rintro x ⟨p, hpout, rfl⟩
    exact ⟨hreference_initials ⟨p, hpout.1, rfl⟩,
      fun hxX ↦ Set.disjoint_left.1 hpout.2 p.initial_mem_support hxX⟩
  · rw [hinitial]
    rintro x ⟨hxcut, hxnotout⟩
    apply hsource_location
    refine ⟨hxcut.1, ?_⟩
    rintro ⟨p, hpY, rfl⟩
    rcases mem_outsideReference_or_support_subset hYclosed hpY with
      hpout | hpinside
    · exact hxnotout ⟨p, hpout, rfl⟩
    · exact hxcut.2 (hpinside p.initial_mem_support)
  · rw [hterminal]
    rintro x ⟨hxcut, hxnotout⟩
    apply hterminal_location
    refine ⟨hxcut.1, ?_⟩
    rintro ⟨p, hpY, hxp⟩
    rcases mem_outsideReference_or_support_subset hYclosed hpY with
      hpout | hpinside
    · exact hxnotout ⟨p, hpout, hxp⟩
    · exact hxcut.2 (hpinside hxp)

/-- When the later row contains the reference row, warp disjointness
automatically supplies all three endpoint-compatibility assumptions of
`of_closedUnderLater_outsideReference`.  Only the two genuine club-stage
location statements remain. -/
theorem OutsideCutBoundary.of_closedUnderLater_outsideReference_of_subset
    {W : Set Gamma.DPath} {before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hWclosed : ClosedUnderPaths Gamma W X)
    (hY : Gamma.IsWarp Y) (hYclosed : ClosedUnderPaths Gamma Y X)
    (hYW : Y ⊆ W)
    (hsource_location :
      Gamma.initialSet W \ Gamma.initialSet Y ⊆ before ∩ innerRoof)
    (hterminal_location :
      Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
        before ∩ outerRoof) :
    OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof := by
  apply OutsideCutBoundary.of_closedUnderLater_outsideReference
    hW hWclosed hY hYclosed
  · rintro x ⟨⟨p, hpW, rfl⟩, q, hqY, hpq⟩
    have heq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW hpW (hYW hqY)
        p.initial_mem_support hpq
    subst q
    exact ⟨p, hqY, rfl⟩
  · rintro x ⟨hxterminal, q, hqY, hxq⟩
    exact ⟨q, hqY,
      DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
        Gamma hW (hYW hqY) hxq hxterminal⟩
  · rintro x ⟨p, hpY, rfl⟩
    exact ⟨p, hYW hpY, rfl⟩
  · exact hsource_location
  · exact hterminal_location

/-- The exact pruned-reference variant of the preceding constructor.

Only reference components which survive outside `X` have to occur in the
later row.  This is strictly weaker than requiring the whole reference row
to occur there, and is the form needed for a ladder reference: its
marker-starting components are deliberately swallowed by the closure, while
its source-starting outside components are retained by the later linkage. -/
theorem OutsideCutBoundary.of_closedUnderLater_outsideReference_of_outsideSubset
    {W : Set Gamma.DPath} {before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hWclosed : ClosedUnderPaths Gamma W X)
    (hY : Gamma.IsWarp Y) (hYclosed : ClosedUnderPaths Gamma Y X)
    (hYW : outsideReference Y X ⊆ W)
    (hsource_location :
      Gamma.initialSet W \ Gamma.initialSet Y ⊆ before ∩ innerRoof)
    (hterminal_location :
      Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
        before ∩ outerRoof) :
    OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof := by
  have hinitial := cutInitial_eq_initialSet_sdiff_of_closedUnderPaths
    (W := W) (X := X) hW hWclosed
  have hterminal := cutTerminal_eq_terminalFrontier_sdiff_of_closedUnderPaths
    (W := W) (X := X) hW hWclosed
  constructor
  · rw [hinitial]
    rintro x ⟨⟨⟨p, hpW, rfl⟩, _hpX⟩, q, hqout, hpq⟩
    have heq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW hpW (hYW hqout)
        p.initial_mem_support hpq
    subst q
    exact ⟨p, hqout, rfl⟩
  · rw [hterminal]
    rintro x ⟨⟨hxterminal, _hxX⟩, q, hqout, hxq⟩
    exact ⟨q, hqout,
      DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
        Gamma hW (hYW hqout) hxq hxterminal⟩
  · rw [hinitial]
    rintro x ⟨p, hpout, rfl⟩
    exact ⟨⟨p, hYW hpout, rfl⟩,
      fun hxX ↦ Set.disjoint_left.1 hpout.2 p.initial_mem_support hxX⟩
  · rw [hinitial]
    rintro x ⟨hxcut, hxnotout⟩
    apply hsource_location
    refine ⟨hxcut.1, ?_⟩
    rintro ⟨p, hpY, rfl⟩
    rcases mem_outsideReference_or_support_subset hYclosed hpY with
      hpout | hpinside
    · exact hxnotout ⟨p, hpout, rfl⟩
    · exact hxcut.2 (hpinside p.initial_mem_support)
  · rw [hterminal]
    rintro x ⟨hxcut, hxnotout⟩
    apply hterminal_location
    refine ⟨hxcut.1, ?_⟩
    rintro ⟨p, hpY, hxp⟩
    rcases mem_outsideReference_or_support_subset hYclosed hpY with
      hpout | hpinside
    · exact hxnotout ⟨p, hpout, hxp⟩
    · exact hxcut.2 (hpinside hxp)

end LinkageBlueprint

namespace Alternating

/-- An interval of backward edges on an omitted reference member is empty,
because the whole alternating path avoids the closed set containing that
member. -/
theorem backwardIntersection_eq_empty_of_not_mem_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    {p : Gamma.DPath} (hpY : p ∈ Y)
    (hpout : p ∉ outsideReference Y X) :
    Q.directionEdges .backward ∩ p.edgeSet = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨heQ, hep⟩
  simp only [AltPath.directionEdges, Set.mem_iUnion] at heQ
  obtain ⟨l, hlQ, _hbackward, hel⟩ := heQ
  have heAlt : e ∈ Q.edgeSet := by
    rw [Q.edgeSet_eq_iUnion_links]
    simp only [Set.mem_iUnion]
    exact ⟨l, hlQ, hel⟩
  have heQvertices := Q.edgeSet_subset_vertexSet_prod heAlt
  have hepvertices := p.edgeSet_subset_support_prod hep
  exact Set.disjoint_left.1
    (disjoint_support_of_not_mem_outsideReference hclosed hQX hpY hpout)
    heQvertices.1 hepvertices.1

/-- Safeness relative to the outside reference lifts to the original full
reference.  This is the exact positive replacement for the false assertion
that Theorem 4.12 paths are automatically endpoint-clean at `X`. -/
theorem IsSafe.lift_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    (hQ : IsSafe (outsideReference Y X) Q) :
    IsSafe Y Q := by
  have hvertexOutside : ∀ {x : V}, x ∈ Q.vertexSet →
      x ∈ Gamma.vertexSet Y → x ∈ Gamma.vertexSet (outsideReference Y X) := by
    intro x hxQ hxY
    obtain ⟨p, hpY, hxp⟩ := hxY
    rcases mem_outsideReference_or_support_subset hclosed hpY with hpout | hpX
    · exact ⟨p, hpout, hxp⟩
    · exact False.elim (Set.disjoint_left.1 hQX hxQ (hpX hxp))
  have hfamily : familyEdges (outsideReference Y X) ⊆ familyEdges Y :=
    familyEdges_outsideReference_subset
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hY, ?_, ?_, ?_⟩
    · intro l hl hbackward
      obtain ⟨p, hpout, hlp⟩ := hQ.1.2.1 l hl hbackward
      exact ⟨p, hpout.1, hlp⟩
    · intro hfirst hinY
      exact hQ.1.2.2.1 hfirst
        (hvertexOutside Q.initial_mem_vertexSet hinY)
    · intro t hterminal hlast htY
      exact hQ.1.2.2.2 t hterminal hlast
        (hvertexOutside (Q.mem_vertexSet_of_terminal_eq hterminal) htY)
  · intro p hpY
    by_cases hpout : p ∈ outsideReference Y X
    · exact hQ.2.1 p hpout
    · left
      exact backwardIntersection_eq_empty_of_not_mem_outsideReference
        hclosed hQX hpY hpout
  · rintro ⟨R, hR⟩
    exact hQ.2.2.1 ⟨R, hR.trans (by
      intro e he
      exact ⟨he.1, fun heout ↦ he.2 (hfamily heout)⟩)⟩
  · rintro ⟨C, hC⟩
    exact hQ.2.2.2 ⟨C, hC.trans (by
      intro e he
      exact ⟨he.1, fun heout ↦ he.2 (hfamily heout)⟩)⟩

/-- The bracket provenance is unchanged when the pruned-reference safe
certificate is lifted. -/
theorem IsBracketSafe.lift_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    (hQ : IsBracketSafe U (outsideReference Y X) Q) :
    IsBracketSafe U Y Q := by
  have hsafe : IsSafe Y Q :=
    IsSafe.lift_outsideReference hclosed hY hQX hQ.1
  exact ⟨hsafe, hsafe.1, hQ.2.2⟩

/-- Avoidance of `X` also upgrades a finite terminal known to be outside
the pruned reference carrier to one outside the full reference carrier. -/
theorem terminal_not_mem_vertexSet_of_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    {v : V} (hterminal : Q.terminal? = some v)
    (hvout : v ∉ Gamma.vertexSet (outsideReference Y X)) :
    v ∉ Gamma.vertexSet Y := by
  intro hvY
  obtain ⟨p, hpY, hvp⟩ := hvY
  rcases mem_outsideReference_or_support_subset hclosed hpY with hpout | hpX
  · exact hvout ⟨p, hpout, hvp⟩
  · exact Set.disjoint_left.1 hQX
      (Q.mem_vertexSet_of_terminal_eq hterminal) (hpX hvp)

/-- Leaving the pruned reference and avoiding the cut implies leaving the
full reference. -/
theorem IsLeaving.lift_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    (hQ : IsLeaving (outsideReference Y X) Q) : IsLeaving Y Q := by
  rcases hQ with hinfinite | ⟨v, hterminal, hvout⟩
  · exact Or.inl hinfinite
  · exact Or.inr ⟨v, hterminal,
      terminal_not_mem_vertexSet_of_outsideReference
        hclosed hQX hterminal hvout⟩

end Alternating

/-! ## Restricting a simultaneous assignment to the full-reference domain -/

namespace Alternating.SimultaneousAssignment

variable {Z : Set Gamma.DPath}

/-- A source uncovered by the full reference is also uncovered by its
outside subreference. -/
def toOutsideSource
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    {x : V // x ∈ Gamma.initialSet Z \
      Gamma.initialSet (outsideReference Y X)} :=
  ⟨z.1, z.property.1,
    fun hz ↦ z.property.2 (initialSet_outsideReference_subset hz)⟩

@[simp] theorem toOutsideSource_val
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    (toOutsideSource (X := X) z : V) = z.1 := rfl

theorem toOutsideSource_injective :
    Function.Injective
      (toOutsideSource (Gamma := Gamma) (Y := Y) (X := X) (Z := Z)) := by
  intro s t hst
  apply Subtype.ext
  exact congrArg
    (fun z : {x : V // x ∈ Gamma.initialSet Z \
      Gamma.initialSet (outsideReference Y X)} ↦ z.1) hst

/-- Restrict an assignment against the outside reference to sources still
uncovered by the full reference, and lift all of its path certificates.

No terminal or source is silently retained: the domain is literally the
full-reference domain, and terminal avoidance is proved from route
avoidance and reference closure. -/
noncomputable def liftOutsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (A : SimultaneousAssignment Z (outsideReference Y X))
    (havoid : ∀ s, Disjoint (A.assigned s).vertexSet X) :
    SimultaneousAssignment Z Y where
  assigned z := A.assigned (toOutsideSource (X := X) z)
  starts_at z := A.starts_at (toOutsideSource (X := X) z)
  safe z := IsSafe.lift_outsideReference hclosed hY
    (havoid (toOutsideSource (X := X) z))
    (A.safe (toOutsideSource (X := X) z))
  leaving z := IsLeaving.lift_outsideReference hclosed
    (havoid (toOutsideSource (X := X) z))
    (A.leaving (toOutsideSource (X := X) z))
  maximal z := by
    rcases A.maximal (toOutsideSource (X := X) z) with hinfinite |
        ⟨v, hv, hterminal⟩
    · exact Or.inl hinfinite
    · exact Or.inr ⟨v,
        ⟨hv.1,
          terminal_not_mem_vertexSet_of_outsideReference hclosed
            (havoid (toOutsideSource (X := X) z)) hterminal hv.2⟩,
        hterminal⟩
  finite_terminals_injective := by
    intro s t v hs ht
    apply toOutsideSource_injective
    exact A.finite_terminals_injective hs ht

@[simp] theorem liftOutsideReference_assigned
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (A : SimultaneousAssignment Z (outsideReference Y X))
    (havoid : ∀ s, Disjoint (A.assigned s).vertexSet X)
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    (liftOutsideReference hclosed hY A havoid).assigned z =
      A.assigned (toOutsideSource (X := X) z) := rfl

end Alternating.SimultaneousAssignment

end Blueprint

/-! Public aliases in the namespace of the alternating predicates.  The
proofs above live beside the Section 9 closure definitions; these aliases
make ordinary field notation available to downstream assignment compilers. -/

namespace Alternating

open Blueprint

variable {V : Type u}
variable {Gamma : DWeb V}
variable {Y U Z : Set Gamma.DPath} {X : Set V}

theorem IsSafe.lift_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    (hQ : IsSafe (outsideReference Y X) Q) :
    IsSafe Y Q :=
  Blueprint.Alternating.IsSafe.lift_outsideReference
    hclosed hY hQX hQ

theorem IsBracketSafe.lift_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    (hQ : IsBracketSafe U (outsideReference Y X) Q) :
    IsBracketSafe U Y Q :=
  Blueprint.Alternating.IsBracketSafe.lift_outsideReference
    hclosed hY hQX hQ

theorem IsLeaving.lift_outsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    {Q : AltPath Gamma.graph} (hQX : Disjoint Q.vertexSet X)
    (hQ : IsLeaving (outsideReference Y X) Q) : IsLeaving Y Q :=
  Blueprint.Alternating.IsLeaving.lift_outsideReference hclosed hQX hQ

namespace SimultaneousAssignment

abbrev toOutsideSource
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    {x : V // x ∈ Gamma.initialSet Z \
      Gamma.initialSet (outsideReference Y X)} :=
  Blueprint.Alternating.SimultaneousAssignment.toOutsideSource z

noncomputable def liftOutsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (A : SimultaneousAssignment Z (outsideReference Y X))
    (havoid : ∀ s, Disjoint (A.assigned s).vertexSet X) :
    SimultaneousAssignment Z Y :=
  Blueprint.Alternating.SimultaneousAssignment.liftOutsideReference
    hclosed hY A havoid

@[simp] theorem liftOutsideReference_assigned
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (A : SimultaneousAssignment Z (outsideReference Y X))
    (havoid : ∀ s, Disjoint (A.assigned s).vertexSet X)
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    (liftOutsideReference hclosed hY A havoid).assigned z =
      A.assigned (toOutsideSource (X := X) z) := rfl

end SimultaneousAssignment
end Alternating

namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

variable {V : Type u}
variable {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {X : Set V}

namespace FracturedAssignmentPeel.BracketFracturedAssignment

variable {Z : _root_.Erdos599.Alternating.FracturedWarp Gamma}

/-- Every selected bracket route avoids the cut when both its literal source
and every recombined forward owner avoid the cut. -/
theorem assigned_disjoint_of_outsideReference
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z
      (outsideReference Y X))
    (hsources : Disjoint (Gamma.initialSet Z.paths) X)
    (hforward : Disjoint (Gamma.vertexSet Z.edgeWarp) X) :
    ∀ s, Disjoint (B.assignment.assigned s).vertexSet X := by
  intro s
  apply disjoint_vertexSet_of_bracketSafe_outsideReference
      (B.bracket_safe s)
  · intro hsX
    exact Set.disjoint_left.1 hsources s.property.1
      (B.assignment.starts_at s ▸ hsX)
  · exact hforward

/-- Lift a bracket assignment made against the outside reference to an
assignment against the full reference.  Its source domain is restricted
exactly as in `SimultaneousAssignment.liftOutsideReference`; no path is
reselected. -/
noncomputable def liftOutsideReference
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z
      (outsideReference Y X))
    (havoid : ∀ s, Disjoint (B.assignment.assigned s).vertexSet X) :
    FracturedAssignmentPeel.BracketFracturedAssignment Z Y where
  assignment := B.assignment.liftOutsideReference hclosed hY havoid
  bracket_safe := by
    intro s
    change IsBracketSafe Z.edgeWarp Y
      (B.assignment.assigned
        (Alternating.SimultaneousAssignment.toOutsideSource
          (X := X) s))
    exact (B.bracket_safe
      (Alternating.SimultaneousAssignment.toOutsideSource
        (X := X) s)).lift_outsideReference
          hclosed hY
          (havoid (Alternating.SimultaneousAssignment.toOutsideSource
            (X := X) s))

/-- The fully geometric constructor used at a linkage-first closed cut. -/
noncomputable def liftOutsideReference_of_disjoint
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z
      (outsideReference Y X))
    (hsources : Disjoint (Gamma.initialSet Z.paths) X)
    (hforward : Disjoint (Gamma.vertexSet Z.edgeWarp) X) :
    FracturedAssignmentPeel.BracketFracturedAssignment Z Y :=
  B.liftOutsideReference hclosed hY
    (B.assigned_disjoint_of_outsideReference hsources hforward)

@[simp] theorem liftOutsideReference_assignment_assigned
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z
      (outsideReference Y X))
    (havoid : ∀ s, Disjoint (B.assignment.assigned s).vertexSet X)
    (s : {x : V // x ∈ Gamma.initialSet Z.paths \
      Gamma.initialSet Y}) :
    (B.liftOutsideReference hclosed hY havoid).assignment.assigned s =
      B.assignment.assigned
        (Alternating.SimultaneousAssignment.toOutsideSource
          (X := X) s) := rfl

/-- Avoidance survives the domain restriction and safeness lift. -/
theorem liftOutsideReference_assignment_disjoint
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment Z
      (outsideReference Y X))
    (havoid : ∀ s, Disjoint (B.assignment.assigned s).vertexSet X) :
    ∀ s,
      Disjoint
        ((B.liftOutsideReference hclosed hY havoid).assignment.assigned s).vertexSet
        X := by
  intro s
  exact havoid
    (Alternating.SimultaneousAssignment.toOutsideSource (X := X) s)

end FracturedAssignmentPeel.BracketFracturedAssignment

namespace OutsideSplitWarp.SplitProjectedOutsideFracturedWarp

variable {W : Set Gamma.DPath}

/-- A later-row-closed cut makes both literal hole sources and their honest
recombined forward owner disjoint from the cut. -/
theorem source_edgeWarp_disjoint_of_closedUnderPaths
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X)
    (hWclosed : ClosedUnderPaths Gamma W X) :
    Disjoint (Gamma.initialSet F.outside.holes.paths) X ∧
      Disjoint (Gamma.vertexSet F.outside.holes.edgeWarp) X := by
  have hcarrier : Disjoint (outsideCarrier W X) X :=
    outsideCarrier_disjoint_of_closedUnderPaths W X hWclosed
  constructor
  · apply Set.disjoint_of_subset_left _ hcarrier
    intro x hx
    rw [← F.outside.vertexSet_eq]
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hp, hpx ▸ p.initial_mem_support⟩
  · rwa [F.edgeWarp_vertexSet_eq]

/-- End-to-end assignment repair for a row-closed literal cut.

The only boundary package required by Theorem 4.12 is the one for the
outside reference subwarp.  The returned assignment is against the original
full reference and every selected route avoids `X`, so the ordinary Claim 2
is applicable without an endpoint-clean hypothesis. -/
theorem exists_fullReferenceBracketAssignment
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X)
    (hWclosed : ClosedUnderPaths Gamma W X)
    (hYclosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    {before innerRoof outerRoof : Set V}
    (hboundary : OutsideCutBoundary
      (Y := outsideReference Y X) W X before innerRoof outerRoof) :
    ∃ B : FracturedAssignmentPeel.BracketFracturedAssignment
        F.outside.holes Y,
      ∀ s, Disjoint (B.assignment.assigned s).vertexSet X := by
  have hYout : Gamma.IsWarp (outsideReference Y X) :=
    outsideReference_isWarp hY
  have hYoutfinite :
      Gamma.HasFiniteCharacter (outsideReference Y X) :=
    outsideReference_finiteCharacter hYfinite
  let B0 := (F.outside.exists_bracketFracturedAssignment
    (hboundary.fractured_boundaryAligned F.outside)
    hYout hYoutfinite
    (hboundary.fractured_referenceInitials F.outside)).some
  have hdisjoint := F.source_edgeWarp_disjoint_of_closedUnderPaths hWclosed
  have havoid : ∀ s, Disjoint (B0.assignment.assigned s).vertexSet X :=
    B0.assigned_disjoint_of_outsideReference hdisjoint.1 hdisjoint.2
  let B := B0.liftOutsideReference hYclosed hY havoid
  exact ⟨B, by
    intro s
    exact havoid
      (Alternating.SimultaneousAssignment.toOutsideSource (X := X) s)⟩

end OutsideSplitWarp.SplitProjectedOutsideFracturedWarp

end LinkageBlueprint

namespace AssignmentClosureContext

open DirectedPath _root_.Erdos599.Alternating

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
variable {Zf : _root_.Erdos599.Alternating.FracturedWarp Gamma}

/-- Route avoidance supplies both interior-disjointness fields and the
noncontained field of the Claim-2 context.  Only the genuine hammock
eligibility statements remain to be supplied by the club-stage boundary. -/
theorem of_disjoint
    (A : SimultaneousAssignment Zf.paths Y)
    (havoid : ∀ s, Disjoint (A.assigned s).vertexSet X)
    (heligibleFinite : ∀ s v,
      (A.assigned s).terminal? = some v →
        HammockEligible before innerRoof outerRoof s.1 (.vertex v))
    (heligibleInfinite : ∀ s, (A.assigned s).IsInfinite →
      HammockEligible before innerRoof outerRoof s.1 .infinity) :
    AssignmentClosureContext A X before innerRoof outerRoof where
  eligible_finite := heligibleFinite
  eligible_infinite := heligibleInfinite
  interior_disjoint_finite := by
    intro s v _hterminal
    apply Set.disjoint_of_subset_left _ (havoid s)
    exact fun _ hx ↦ hx.1
  interior_disjoint_infinite := by
    intro s _hinfinite
    apply Set.disjoint_of_subset_left _ (havoid s)
    exact fun _ hx ↦ hx.1
  outside := by
    intro s hsubset
    exact Set.disjoint_left.1 (havoid s)
      (A.assigned s).initial_mem_vertexSet
      (hsubset (A.assigned s).initial_mem_vertexSet)

end AssignmentClosureContext
end Blueprint

end Erdos599
