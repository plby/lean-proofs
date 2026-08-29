/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintReplacement
import ErdosProblems.Erdos599.PathFilterComponents
import ErdosProblems.Erdos599.AlternatingDichotomy
import ErdosProblems.Erdos599.BoundarySimultaneousAssignment

/-!
# The cut-dependent outside family in Assertion 9.31

For a warp `W` and a closing set `X`, the paper writes `W ↾ X` for the
fractured family of the non-`X` holes of `W`.  Its edge set is

`familyEdges W \ (X ×ˢ X)`.

The filtered edge relation is decomposed into its forward root orbits.  The
result is an honest finite-character warp with exactly the filtered edge set
and exactly the required carrier (including isolated vertices of `W` outside
`X`).  It supplies the honest `edgeWarp` certificate of the literal fractured
family, but it is not substituted for that family: doing so would amalgamate
two holes meeting at `X` and would destroy the closure conclusion of Claim 2.

The split construction then duplicates every cut vertex into an incoming and
an outgoing occurrence and decomposes that relation into its finite root
orbits.  Thus the literal fragment initials and terminals are not confused
with the roots and sinks of the recombined relation.

The final part isolates the two genuinely cut-dependent facts about the
assignment selected in 9.31.  Its trace meets `X` only at the prescribed
endpoints and has a vertex outside `X`.  Together with the root/sink location
of the split relation, these facts *prove* `AssignmentClosureContext`.
They are strictly below that record: eligibility is derived from the actual
initial and terminal frontiers, and both disjointness fields are derived from
the literal intersection formula.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-! ## The honest occurrence-split boundary problem -/

namespace CutDuplication

open FracturedDuplication

/-- Lift the reference warp using the same endpoint roles as the fractured
family: outgoing at an initial, incoming at a nontrivial finite terminal, and
plain internally.  This differs deliberately from `liftedReference`, which
expands every reference vertex through all three copies and is suited to a
different normalized-web reduction. -/
noncomputable def endpointLiftedReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) :
    Set (web Gamma Z).DPath :=
  liftPath Z '' Y

theorem endpointLiftedReference_isWarp
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hY : Gamma.IsWarp Y) :
    (web Gamma Z).IsWarp (endpointLiftedReference Z Y) := by
  intro P hP Q hQ hPQ
  rcases hP with ⟨p, hp, rfl⟩
  rcases hQ with ⟨q, hq, rfl⟩
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hPQ rfl
  change Disjoint (liftPath Z p).support (liftPath Z q).support
  rw [Set.disjoint_left]
  intro z hzp hzq
  rcases (mem_support_liftPath Z p z).1 hzp with ⟨x, hxp, hxz⟩
  rcases (mem_support_liftPath Z q z).1 hzq with ⟨y, hyq, hyz⟩
  have hxy : x = y := by
    simpa only [project_occurrence] using
      congrArg project (hxz.trans hyz.symm)
  subst y
  exact Set.disjoint_left.1 (hY hp hq hpq) hxp hyq

theorem endpointLiftedReference_hasFiniteCharacter
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y) :
    (web Gamma Z).HasFiniteCharacter (endpointLiftedReference Z Y) := by
  intro P hP
  rcases hP with ⟨p, hp, rfl⟩
  rcases hYfinite hp with ⟨q, rfl⟩
  exact ⟨mapFinitePath (occurrence Z (Sum.inl q))
    (occurrence_injective Z (Sum.inl q))
    (web_adj_occurrence Z (Sum.inl q)) q, rfl⟩

theorem initialSet_endpointLiftedReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) :
    (web Gamma Z).initialSet (endpointLiftedReference Z Y) =
      sourceCopy Z '' Gamma.initialSet Y := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    rw [initial_liftPath, occurrence_initial] at hP
    exact ⟨p.initial, ⟨p, hp, rfl⟩, hP⟩
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    refine ⟨liftPath Z p, ⟨p, hp, rfl⟩, ?_⟩
    rw [initial_liftPath, occurrence_initial, hpx]

/-- Literal boundary alignment survives occurrence splitting when the
reference warp is endpoint-role lifted.  In particular, trivial members need
no special case: a lifted reference member meeting the terminal copy already
has the same role, and warp disjointness identifies it with the member whose
original terminal is supplied by boundary alignment. -/
theorem boundaryAligned_endpointLifted
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y) (hY : Gamma.IsWarp Y) :
    BoundaryAligned (liftedPaths Z) (endpointLiftedReference Z Y) := by
  constructor
  · rintro z ⟨hzInitial, hzY⟩
    rw [initialSet_liftedPaths] at hzInitial
    rcases hzInitial with ⟨x, hxInitial, rfl⟩
    rcases hzY with ⟨Q, ⟨q, hqY, rfl⟩, hzq⟩
    rcases (mem_support_liftPath Z q (sourceCopy Z x)).1 hzq with
      ⟨y, hyq, hy⟩
    have hyx : y = x := by
      simpa only [project_occurrence, project_sourceCopy] using
        congrArg project hy
    subst y
    have hxY : x ∈ Gamma.vertexSet Y := ⟨q, hqY, hyq⟩
    have hxYInitial : x ∈ Gamma.initialSet Y :=
      hboundary.1 ⟨hxInitial, hxY⟩
    rw [initialSet_endpointLiftedReference]
    exact ⟨x, hxYInitial, rfl⟩
  · rintro z ⟨hzTerminal, hzY⟩
    rcases hzTerminal with ⟨P, ⟨p, hpZ, rfl⟩, hpterm⟩
    rcases hzY with ⟨Q, ⟨q, hqY, rfl⟩, hzq⟩
    rcases (mem_support_liftPath Z q z).1 hzq with
      ⟨x, hxq, hxz⟩
    have hxproject : x = project z := by
      simpa only [project_occurrence] using congrArg project hxz
    have hptermProject : Gamma.terminal? p = some (project z) := by
      have hmap := congrArg (Option.map project) hpterm
      rw [terminal_liftPath_projected] at hmap
      simpa only [Option.map_some] using hmap
    have hptermOriginal : Gamma.terminal? p = some x := by
      simpa only [hxproject] using hptermProject
    have hxY : x ∈ Gamma.vertexSet Y := ⟨q, hqY, hxq⟩
    rcases hboundary.2 ⟨⟨p, hpZ, hptermOriginal⟩, hxY⟩ with
      ⟨r, hrY, hrterm⟩
    have hqr : q = r :=
      DWeb.IsWarp.eq_of_mem_support hY hqY hrY hxq
        (Gamma.terminal_mem_support hrterm)
    subst r
    refine ⟨liftPath Z q, ⟨q, hqY, rfl⟩, ?_⟩
    change (liftPath Z q).terminal? = some z
    have hrterm' : q.terminal? = some x := by
      simpa [DWeb.terminal?] using hrterm
    rw [terminal_liftPath, hrterm']
    exact congrArg some hxz

/-- Reference initials remain reference initials in the occurrence-split
problem. -/
theorem initialSet_endpointLiftedReference_subset
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    (web Gamma Z).initialSet (endpointLiftedReference Z Y) ⊆
      (web Gamma Z).initialSet (liftedPaths Z) := by
  rw [initialSet_endpointLiftedReference, initialSet_liftedPaths]
  exact Set.image_mono hinitial

/-- The nontrivial members of the occurrence-split fractured family.  Trivial
holes are handled directly before invoking the expanded-reference theorem. -/
noncomputable def nontrivialLiftedPaths (Z : FracturedWarp Gamma) :
    Set (web Gamma Z).DPath :=
  liftPath Z '' {p | p ∈ Z.paths ∧ PathNontrivial p}

theorem nontrivialLiftedPaths_isWarp (Z : FracturedWarp Gamma) :
    (web Gamma Z).IsWarp (nontrivialLiftedPaths Z) := by
  intro P hP Q hQ hPQ
  apply liftedPaths_isWarp Z
  · rcases hP with ⟨p, hp, rfl⟩
    exact ⟨p, hp.1, rfl⟩
  · rcases hQ with ⟨q, hq, rfl⟩
    exact ⟨q, hq.1, rfl⟩
  · exact hPQ

theorem nontrivialLiftedPaths_hasFiniteCharacter (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) :
    (web Gamma Z).HasFiniteCharacter (nontrivialLiftedPaths Z) := by
  rintro P ⟨p, hp, rfl⟩
  rcases hZfinite hp.1 with ⟨q, rfl⟩
  exact ⟨mapFinitePath (occurrence Z (Sum.inl q))
    (occurrence_injective Z (Sum.inl q))
    (web_adj_occurrence Z (Sum.inl q)) q, rfl⟩

theorem initialSet_nontrivialLiftedPaths (Z : FracturedWarp Gamma) :
    (web Gamma Z).initialSet (nontrivialLiftedPaths Z) =
      sourceCopy Z '' Gamma.initialSet {p | p ∈ Z.paths ∧ PathNontrivial p} := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    rw [initial_liftPath, occurrence_initial] at hP
    exact ⟨p.initial, ⟨p, hp, rfl⟩, hP⟩
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    refine ⟨liftPath Z p, ⟨p, hp, rfl⟩, ?_⟩
    rw [initial_liftPath, occurrence_initial, hpx]

/-- After removing trivial holes, the expanded reference has the exact
boundary alignment needed for Remark 4.20.  Its connector edges prevent an
assignment from stopping prematurely at the incoming copy of a covered
fracture vertex. -/
theorem boundaryAligned_nontrivial_expanded
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hYfinite : Gamma.HasFiniteCharacter Y) :
    BoundaryAligned (nontrivialLiftedPaths Z) (liftedReference Z Y) := by
  constructor
  · rintro z ⟨hzInitial, hzY⟩
    rw [initialSet_nontrivialLiftedPaths] at hzInitial
    rcases hzInitial with ⟨x, hxInitial, rfl⟩
    rw [vertexSet_liftedReference Z hYfinite] at hzY
    rcases hzY with ⟨y, hyY, hxy⟩
    have hyx : y = x := by
      have hp := mem_vertexBlock_project Z hxy
      simpa only [project_sourceCopy] using hp.symm
    subst y
    have hxZInitial : x ∈ Gamma.initialSet Z.paths := by
      rcases hxInitial with ⟨p, hp, hpinitial⟩
      exact ⟨p, hp.1, hpinitial⟩
    have hxYInitial : x ∈ Gamma.initialSet Y :=
      hboundary.1 ⟨hxZInitial, hyY⟩
    rw [initialSet_liftedReference Z hYfinite]
    exact ⟨x, hxYInitial, rfl⟩
  · rintro z ⟨hzTerminal, hzY⟩
    rcases hzTerminal with ⟨P, ⟨p, hp, rfl⟩, hpterm⟩
    rw [vertexSet_liftedReference Z hYfinite] at hzY
    rcases hzY with ⟨x, hxY, hzx⟩
    have hzproject : project z = x := mem_vertexBlock_project Z hzx
    have hptermProject : Gamma.terminal? p = some (project z) := by
      have hmap := congrArg (Option.map project) hpterm
      rw [terminal_liftPath_projected] at hmap
      simpa only [Option.map_some] using hmap
    have hptermOriginal : Gamma.terminal? p = some x := by
      simpa only [hzproject] using hptermProject
    rcases hboundary.2 ⟨⟨p, hp.1, hptermOriginal⟩, hxY⟩ with
      ⟨r, hrY, hrterm⟩
    have hzIncoming : z = incoming x := by
      have hpterm' : p.terminal? = some x := by
        simpa [DWeb.terminal?] using hptermOriginal
      have hlift : (liftPath Z p).terminal? =
          some (occurrence Z p x) := by
        rw [terminal_liftPath, hpterm']
        rfl
      have hptermLift : (liftPath Z p).terminal? = some z := by
        simpa [DWeb.terminal?] using hpterm
      have hzocc : z = occurrence Z p x :=
        Option.some.inj (hptermLift.symm.trans hlift)
      rw [hzocc]
      have hne : x ≠ p.initial :=
        (initial_ne_terminal_of_nontrivial hp.2 hptermOriginal).symm
      simp [occurrence, hne, hpterm']
    rcases hYfinite hrY with ⟨rfin, hr⟩
    subst r
    have hrfinish : rfin.finish = x := Option.some.inj hrterm
    refine ⟨Sum.inl (expandFinitePath Z rfin), ⟨rfin, hrY, rfl⟩, ?_⟩
    change some (terminalCopy Z rfin.finish) = some z
    rw [hrfinish, hzIncoming]
    rfl

theorem initialSet_liftedReference_subset_nontrivial
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆
      Gamma.initialSet {p | p ∈ Z.paths ∧ PathNontrivial p}) :
    (web Gamma Z).initialSet (liftedReference Z Y) ⊆
      (web Gamma Z).initialSet (nontrivialLiftedPaths Z) := by
  rw [initialSet_liftedReference Z hYfinite,
    initialSet_nontrivialLiftedPaths]
  exact Set.image_mono hinitial

/-- Correct expanded-reference split assignment, under the explicit
condition that reference initials are witnessed by nontrivial holes.  The
general compiler obtains that condition after peeling trivial-only covered
components. -/
theorem exists_nontrivialExpandedAssignment
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆
      Gamma.initialSet {p | p ∈ Z.paths ∧ PathNontrivial p}) :
    Nonempty (SimultaneousAssignment
      (nontrivialLiftedPaths Z) (liftedReference Z Y)) := by
  exact boundarySimultaneousAssignmentStatement (web Gamma Z)
    (nontrivialLiftedPaths Z) (liftedReference Z Y)
    (boundaryAligned_nontrivial_expanded Z hboundary hYfinite)
    (nontrivialLiftedPaths_isWarp Z)
    (liftedReference_isWarp Z hY)
    (nontrivialLiftedPaths_hasFiniteCharacter Z hZfinite)
    (liftedReference_hasFiniteCharacter Z Y)
    (initialSet_liftedReference_subset_nontrivial Z hYfinite hinitial)

/-- An honest assignment problem obtained from the endpoint-role lift.

This theorem is useful for auditing the boundary identities, but is *not* the
input to the final projection compiler.  A finite assignment may stop at an
incoming fracture copy whose outgoing copy lies on a trivial reference path;
after projection that endpoint is covered.  Remark 4.20 therefore uses the
expanded reference with connector edges, peels trivial holes, and contracts
those connectors before maximal-run compression. -/
theorem exists_endpointLiftedAssignment
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (SimultaneousAssignment
      (liftedPaths Z) (endpointLiftedReference Z Y)) := by
  exact boundarySimultaneousAssignmentStatement (web Gamma Z)
    (liftedPaths Z) (endpointLiftedReference Z Y)
    (boundaryAligned_endpointLifted Z hboundary hY)
    (liftedPaths_isWarp Z)
    (endpointLiftedReference_isWarp Z hY)
    (liftedPaths_hasFiniteCharacter Z hZfinite)
    (endpointLiftedReference_hasFiniteCharacter Z hYfinite)
    (initialSet_endpointLiftedReference_subset Z hinitial)

end CutDuplication

/-! ## Root and sink formulas for a general forward orientation -/

namespace CutOrientation

variable {D : Digraph V}

private theorem walk_exists_outgoing_of_mem_support_of_ne_finish :
    ∀ {a b x : V} (p : Walk D a b),
      x ∈ p.support → x ≠ b → ∃ y, (x, y) ∈ p.edgeSet
  | a, _, x, .nil, hx, hne => by
      have : x = a := by simpa using hx
      exact (hne this).elim
  | a, b, x, .cons (v := c) edge p, hx, hne => by
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨c, by simp⟩
      · obtain ⟨y, hy⟩ :=
          walk_exists_outgoing_of_mem_support_of_ne_finish p hx hne
        exact ⟨y, by simp [hy]⟩

private theorem path_exists_outgoing_of_mem_support_of_not_terminal
    (p : Path D) {x : V} (hx : x ∈ p.support)
    (hterm : p.terminal? ≠ some x) :
    ∃ y, (x, y) ∈ p.edgeSet := by
  rcases p with p | r
  · have hne : x ≠ p.finish := by
      intro h
      exact hterm (by simp [h])
    exact walk_exists_outgoing_of_mem_support_of_ne_finish p.walk hx hne
  · obtain ⟨n, hn⟩ := hx
    refine ⟨r (n + 1), ?_⟩
    exact ⟨n, congrArg (fun z ↦ (z, r (n + 1))) hn.symm⟩

/-- A carrier vertex is a root precisely when no oriented edge enters it. -/
theorem isRoot_iff_noIncoming (O : ForwardOrientation D) {x : V} :
    O.IsRoot x ↔ x ∈ O.carrier ∧ ¬ ∃ y, (y, x) ∈ O.edge := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    rintro ⟨y, hyx⟩
    have hstep := O.depth_step hyx
    rw [hx.2] at hstep
    omega
  · rintro ⟨hxcarrier, hnoin⟩
    refine ⟨hxcarrier, ?_⟩
    by_contra hdepth
    have hpos : 0 < O.depth x := Nat.pos_of_ne_zero hdepth
    exact hnoin (O.predecessor hxcarrier hpos)

/-- Initials of the root-orbit family are exactly relation roots. -/
theorem initialSet_rootPaths (G : DWeb V)
    (O : ForwardOrientation G.graph) :
    G.initialSet O.rootPaths = {x | O.IsRoot x} := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases hp with ⟨r, rfl⟩
    change O.IsRoot x
    have hinit : (O.rootPath r).initial = r.1 := O.rootPath_initial r
    exact hpx ▸ hinit ▸ r.2
  · intro hx
    let r : O.Root := ⟨x, hx⟩
    exact ⟨O.rootPath r, ⟨r, rfl⟩, O.rootPath_initial r⟩

/-- Initials of the root-orbit family in carrier/edge language. -/
theorem initialSet_rootPaths_eq_noIncoming (G : DWeb V)
    (O : ForwardOrientation G.graph) :
    G.initialSet O.rootPaths =
      {x | x ∈ O.carrier ∧ ¬ ∃ y, (y, x) ∈ O.edge} := by
  rw [initialSet_rootPaths]
  ext x
  exact isRoot_iff_noIncoming O

/-- Finite terminals of the root-orbit family are exactly relation sinks. -/
theorem terminalFrontier_rootPaths_eq_noOutgoing (G : DWeb V)
    (O : ForwardOrientation G.graph) :
    G.terminalFrontier O.rootPaths =
      {x | x ∈ O.carrier ∧ ¬ ∃ y, (x, y) ∈ O.edge} := by
  ext x
  constructor
  · rintro ⟨p, hp, hterm⟩
    rcases hp with ⟨r, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← PathFilterComponents.ForwardOrientation.vertexSet_rootPaths G O]
      exact ⟨O.rootPath r, ⟨r, rfl⟩, G.terminal_mem_support hterm⟩
    · simp only [ForwardOrientation.rootPath] at hterm
      split at hterm <;> rename_i hstop
      · exact nomatch hterm
      · simp only [DWeb.terminal?, Path.terminal?, Option.some.injEq] at hterm
        subst x
        exact O.not_hasNext_stoppingIndex hstop
  · rintro ⟨hxcarrier, hnoout⟩
    by_contra hnotterminal
    have hxvertex : x ∈ G.vertexSet O.rootPaths := by
      rw [PathFilterComponents.ForwardOrientation.vertexSet_rootPaths G O]
      exact hxcarrier
    obtain ⟨p, hp, hxp⟩ := hxvertex
    have hpterm : G.terminal? p ≠ some x := by
      intro h
      exact hnotterminal ⟨p, hp, h⟩
    have hpterm' : p.terminal? ≠ some x := by
      simpa [DWeb.terminal?, Path.terminal?] using hpterm
    obtain ⟨y, hy⟩ :=
      path_exists_outgoing_of_mem_support_of_not_terminal p hxp hpterm'
    apply hnoout
    refine ⟨y, ?_⟩
    rw [← O.rootPathEdges_eq]
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hy⟩⟩

end CutOrientation

/-! ## Filtering a finite-character warp at a closing set -/

/-- Edges of `W` which do not have both endpoints in `X`.  This is the
literal edge formula `E[W ↾ X] = E[W] \ E[W[X]]`. -/
def outsideFamilyEdges (W : Set Gamma.DPath) (X : Set V) : Set (V × V) :=
  familyEdges W \ (X ×ˢ X)

/-- Vertices which must survive the outside-edge decomposition.  All
vertices of `W` outside `X` survive, as do the endpoints in `X` of retained
edges. -/
def outsideCarrier (W : Set Gamma.DPath) (X : Set V) : Set V :=
  (Gamma.vertexSet W \ X) ∪
    {x | ∃ y, (x, y) ∈ outsideFamilyEdges W X ∨
      (y, x) ∈ outsideFamilyEdges W X}

theorem outsideFamilyEdges_subset (W : Set Gamma.DPath) (X : Set V) :
    outsideFamilyEdges W X ⊆ familyEdges W :=
  Set.sdiff_subset

theorem outsideFamilyEdges_endpoints (W : Set Gamma.DPath) (X : Set V)
    {e : V × V} (he : e ∈ outsideFamilyEdges W X) :
    e.1 ∈ outsideCarrier W X ∧ e.2 ∈ outsideCarrier W X := by
  constructor
  · exact Or.inr ⟨e.2, Or.inl he⟩
  · exact Or.inr ⟨e.1, Or.inr he⟩

/-- If a set happens to contain every member of `W` which it meets, then no
retained outside edge is incident with that set.  Consequently the entire
outside carrier is disjoint from it.

This conditional lemma is useful for auxiliary closed families, but its
hypothesis must **not** be attributed to the linkage fractured in Assertion
9.31: those linkage paths are allowed to cross the closing set, and their
outside pieces are precisely the holes used by that assertion. -/
theorem outsideCarrier_disjoint_of_closedUnderPaths
    (W : Set Gamma.DPath) (X : Set V)
    (hclosed : ClosedUnderPaths Gamma W X) :
    Disjoint (outsideCarrier W X) X := by
  rw [Set.disjoint_left]
  intro x hxCarrier hxX
  rcases hxCarrier with hxOutside | hxIncident
  · exact hxOutside.2 hxX
  · obtain ⟨y, hxy | hyx⟩ := hxIncident
    · have hxyW : (x, y) ∈ familyEdges W := hxy.1
      simp only [familyEdges, Set.mem_iUnion] at hxyW
      obtain ⟨p, hpW, hxyP⟩ := hxyW
      have hend := p.edgeSet_subset_support_prod hxyP
      have hpX : p.support ⊆ X :=
        hclosed p hpW ⟨x, hend.1, hxX⟩
      exact hxy.2 ⟨hxX, hpX hend.2⟩
    · have hyxW : (y, x) ∈ familyEdges W := hyx.1
      simp only [familyEdges, Set.mem_iUnion] at hyxW
      obtain ⟨p, hpW, hyxP⟩ := hyxW
      have hend := p.edgeSet_subset_support_prod hyxP
      have hpX : p.support ⊆ X :=
        hclosed p hpW ⟨x, hend.2, hxX⟩
      exact hyx.2 ⟨hpX hend.1, hxX⟩

/-! ## Splitting the filtered relation at the cut

The recombined filtered relation is not itself the literal family of holes:
at a vertex of `X` an incoming hole must stop and an outgoing hole must
start.  The following relation performs exactly that split.  It is the
graph-theoretic core of `W ↾ X`, before its honest split paths are projected
back to the original vertex type.
-/

namespace CutSplit

open FracturedDuplication

/-- The occurrence used at the tail of a retained edge. -/
noncomputable def tailCopy (X : Set V) (x : V) : Vertex V :=
  by
    classical
    exact if x ∈ X then outgoing x else plain x

/-- The occurrence used at the head of a retained edge. -/
noncomputable def headCopy (X : Set V) (x : V) : Vertex V :=
  by
    classical
    exact if x ∈ X then incoming x else plain x

@[simp] theorem project_tailCopy (X : Set V) (x : V) :
    project (tailCopy X x) = x := by
  simp only [tailCopy]
  split <;> rfl

@[simp] theorem project_headCopy (X : Set V) (x : V) :
    project (headCopy X x) = x := by
  simp only [headCopy]
  split <;> rfl

theorem tailCopy_injective (X : Set V) : Function.Injective (tailCopy X) := by
  intro x y h
  simpa only [project_tailCopy] using congrArg project h

theorem headCopy_injective (X : Set V) : Function.Injective (headCopy X) := by
  intro x y h
  simpa only [project_headCopy] using congrArg project h

/-- Every retained edge, with its two cut-dependent endpoint roles. -/
def edge (E : Set (V × V)) (X : Set V) : Set (Vertex V × Vertex V) :=
  {e | ∃ x y, (x, y) ∈ E ∧ e = (tailCopy X x, headCopy X y)}

theorem mem_edge_iff {E : Set (V × V)} {X : Set V}
    {a b : Vertex V} :
    (a, b) ∈ edge E X ↔
      (project a, project b) ∈ E ∧
        a = tailCopy X (project a) ∧ b = headCopy X (project b) := by
  constructor
  · rintro ⟨x, y, hxy, heq⟩
    have ha : a = tailCopy X x := congrArg Prod.fst heq
    have hb : b = headCopy X y := congrArg Prod.snd heq
    subst a
    subst b
    simp only [project_tailCopy, project_headCopy]
    exact ⟨hxy, trivial, trivial⟩
  · rintro ⟨hab, ha, hb⟩
    refine ⟨project a, project b, hab, ?_⟩
    exact Prod.ext ha hb

theorem project_edge_image (E : Set (V × V)) (X : Set V) :
    (fun e : Vertex V × Vertex V ↦ (project e.1, project e.2)) ''
      edge E X = E := by
  ext e
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_edge_iff.1 hz).1
  · intro he
    refine ⟨(tailCopy X e.1, headCopy X e.2), ?_, ?_⟩
    · exact ⟨e.1, e.2, he, rfl⟩
    · simp

/-- The split carrier.  Non-cut vertices have one plain occurrence; a cut
vertex has an outgoing occurrence exactly when a retained edge leaves it and
an incoming occurrence exactly when a retained edge enters it. -/
def carrier (C : Set V) (E : Set (V × V)) (X : Set V) : Set (Vertex V) :=
  plain '' (C \ X) ∪
    outgoing '' {x | x ∈ X ∧ ∃ y, (x, y) ∈ E} ∪
    incoming '' {x | x ∈ X ∧ ∃ y, (y, x) ∈ E}

/-- Original vertices which are initials of literal cut fragments. -/
def initialVertices (C : Set V) (E : Set (V × V)) (X : Set V) : Set V :=
  {x | (x ∈ X ∧ ∃ y, (x, y) ∈ E) ∨
    (x ∈ C ∧ x ∉ X ∧ ¬ ∃ y, (y, x) ∈ E)}

/-- Original vertices which are finite terminals of literal cut fragments. -/
def terminalVertices (C : Set V) (E : Set (V × V)) (X : Set V) : Set V :=
  {x | (x ∈ X ∧ ∃ y, (y, x) ∈ E) ∨
    (x ∈ C ∧ x ∉ X ∧ ¬ ∃ y, (x, y) ∈ E)}

theorem mem_carrier_iff {C : Set V} {E : Set (V × V)} {X : Set V}
    {z : Vertex V} :
    z ∈ carrier C E X ↔
      (z = plain (project z) ∧ project z ∈ C \ X) ∨
      (z = outgoing (project z) ∧ project z ∈ X ∧
        ∃ y, (project z, y) ∈ E) ∨
      (z = incoming (project z) ∧ project z ∈ X ∧
        ∃ y, (y, project z) ∈ E) := by
  constructor
  · intro hz
    rcases hz with (hz | hz) | hz
    · rcases hz with ⟨x, hx, rfl⟩
      exact Or.inl ⟨rfl, hx⟩
    · rcases hz with ⟨x, hx, rfl⟩
      exact Or.inr (Or.inl ⟨rfl, hx⟩)
    · rcases hz with ⟨x, hx, rfl⟩
      exact Or.inr (Or.inr ⟨rfl, hx⟩)
  · rintro (⟨hz, hx⟩ | ⟨hz, hx⟩ | ⟨hz, hx⟩)
    · exact Or.inl (Or.inl ⟨project z, hx, hz.symm⟩)
    · exact Or.inl (Or.inr ⟨project z, hx, hz.symm⟩)
    · exact Or.inr ⟨project z, hx, hz.symm⟩

/-- Outside the cut the split carrier has a unique occurrence over each
original vertex. -/
theorem eq_of_mem_carrier_of_project_eq_of_not_mem
    {C : Set V} {E : Set (V × V)} {X : Set V}
    {a b : Vertex V} (ha : a ∈ carrier C E X)
    (hb : b ∈ carrier C E X) (hab : project a = project b)
    (haX : project a ∉ X) : a = b := by
  rw [mem_carrier_iff] at ha hb
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · rw [ha.1, hb.1, hab]
    · exact (haX (hab ▸ hb.2.1)).elim
    · exact (haX (hab ▸ hb.2.1)).elim
  · exact (haX ha.2.1).elim
  · exact (haX ha.2.1).elim

/-- A split root over a cut vertex is its outgoing occurrence. -/
theorem root_eq_outgoing_of_project_mem
    {C : Set V} {E : Set (V × V)} {X : Set V}
    {z : Vertex V} (hz : z ∈ carrier C E X)
    (hroot : ¬ ∃ a, (a, z) ∈ edge E X)
    (hzX : project z ∈ X) : z = outgoing (project z) := by
  rw [mem_carrier_iff] at hz
  rcases hz with hz | hz | hz
  · exact (hz.2.2 hzX).elim
  · exact hz.1
  · obtain ⟨a, ha⟩ := hz.2.2
    exact (hroot ⟨tailCopy X a, ⟨a, project z, ha,
      by rw [hz.1]; simp [headCopy, hzX]⟩⟩).elim

/-- A split sink over a cut vertex is its incoming occurrence. -/
theorem sink_eq_incoming_of_project_mem
    {C : Set V} {E : Set (V × V)} {X : Set V}
    {z : Vertex V} (hz : z ∈ carrier C E X)
    (hsink : ¬ ∃ b, (z, b) ∈ edge E X)
    (hzX : project z ∈ X) : z = incoming (project z) := by
  rw [mem_carrier_iff] at hz
  rcases hz with hz | hz | hz
  · exact (hz.2.2 hzX).elim
  · obtain ⟨b, hb⟩ := hz.2.2
    exact (hsink ⟨headCopy X b, ⟨project z, b, hb,
      by rw [hz.1]; simp [tailCopy, hzX]⟩⟩).elim
  · exact hz.1

/-- The ambient split web has exactly the original graph edges between all
endpoint roles.  The filtered relation below uses only its prescribed
tail/head roles and contains no connector edges. -/
def web (Gamma : DWeb V) : DWeb (Vertex V) where
  graph.Adj a b := Gamma.graph.Adj (project a) (project b)
  source := project ⁻¹' Gamma.source
  target := project ⁻¹' Gamma.target

theorem edge_in_graph {E : Set (V × V)} {X : Set V}
    (hE : E ⊆ {e | Gamma.graph.Adj e.1 e.2}) :
    edge E X ⊆ {e | (web Gamma).graph.Adj e.1 e.2} := by
  rintro ⟨a, b⟩ hab
  exact hE (mem_edge_iff.1 hab).1

theorem edge_endpoints {C : Set V} {E : Set (V × V)} {X : Set V}
    (hendpoints : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C) :
    ∀ e ∈ edge E X, e.1 ∈ carrier C E X ∧
      e.2 ∈ carrier C E X := by
  rintro ⟨a, b⟩ hab
  rcases hab with ⟨x, y, hxy, heq⟩
  have ha : a = tailCopy X x := congrArg Prod.fst heq
  have hb : b = headCopy X y := congrArg Prod.snd heq
  subst a
  subst b
  have hends := hendpoints (x, y) hxy
  constructor
  · by_cases hx : x ∈ X
    · exact Or.inl (Or.inr ⟨x, ⟨hx, y, hxy⟩, by simp [tailCopy, hx]⟩)
    · exact Or.inl (Or.inl ⟨x, ⟨hends.1, hx⟩,
        by simp [tailCopy, hx]⟩)
  · by_cases hy : y ∈ X
    · exact Or.inr ⟨y, ⟨hy, x, hxy⟩, by simp [headCopy, hy]⟩
    · exact Or.inl (Or.inl ⟨y, ⟨hends.2, hy⟩,
        by simp [headCopy, hy]⟩)

theorem project_roots {C : Set V} {E : Set (V × V)} {X : Set V} :
    project '' {z | z ∈ carrier C E X ∧
      ¬ ∃ a, (a, z) ∈ edge E X} = initialVertices C E X := by
  ext x
  constructor
  · rintro ⟨z, ⟨hzCarrier, hzRoot⟩, rfl⟩
    rcases hzCarrier with (hzPlain | hzOutgoing) | hzIncoming
    · rcases hzPlain with ⟨y, ⟨hyC, hyX⟩, rfl⟩
      right
      refine ⟨hyC, hyX, ?_⟩
      rintro ⟨a, hay⟩
      apply hzRoot
      refine ⟨tailCopy X a, ?_⟩
      exact ⟨a, y, hay, by simp [headCopy, hyX]⟩
    · rcases hzOutgoing with ⟨y, ⟨hyX, t, hyt⟩, rfl⟩
      exact Or.inl ⟨hyX, t, hyt⟩
    · rcases hzIncoming with ⟨y, ⟨hyX, a, hay⟩, rfl⟩
      exfalso
      apply hzRoot
      exact ⟨tailCopy X a, ⟨a, y, hay, by simp [headCopy, hyX]⟩⟩
  · rintro (hxCut | hxOutside)
    · rcases hxCut with ⟨hxX, y, hxy⟩
      refine ⟨outgoing x, ⟨?_, ?_⟩, rfl⟩
      · exact Or.inl (Or.inr ⟨x, ⟨hxX, y, hxy⟩, rfl⟩)
      · rintro ⟨a, ha⟩
        have ha' := mem_edge_iff.1 ha
        have hrole := congrArg Prod.snd ha'.2.2
        simp [headCopy, project, hxX, incoming, outgoing] at hrole
    · rcases hxOutside with ⟨hxC, hxX, hxNoIn⟩
      refine ⟨plain x, ⟨?_, ?_⟩, rfl⟩
      · exact Or.inl (Or.inl ⟨x, ⟨hxC, hxX⟩, rfl⟩)
      · rintro ⟨a, ha⟩
        exact hxNoIn ⟨project a, (mem_edge_iff.1 ha).1⟩

theorem project_sinks {C : Set V} {E : Set (V × V)} {X : Set V} :
    project '' {z | z ∈ carrier C E X ∧
      ¬ ∃ b, (z, b) ∈ edge E X} = terminalVertices C E X := by
  ext x
  constructor
  · rintro ⟨z, ⟨hzCarrier, hzSink⟩, rfl⟩
    rcases hzCarrier with (hzPlain | hzOutgoing) | hzIncoming
    · rcases hzPlain with ⟨y, ⟨hyC, hyX⟩, rfl⟩
      right
      refine ⟨hyC, hyX, ?_⟩
      rintro ⟨b, hyb⟩
      apply hzSink
      exact ⟨headCopy X b, ⟨y, b, hyb, by simp [tailCopy, hyX]⟩⟩
    · rcases hzOutgoing with ⟨y, ⟨hyX, b, hyb⟩, rfl⟩
      exfalso
      apply hzSink
      exact ⟨headCopy X b, ⟨y, b, hyb, by simp [tailCopy, hyX]⟩⟩
    · rcases hzIncoming with ⟨y, ⟨hyX, a, hay⟩, rfl⟩
      exact Or.inl ⟨hyX, a, hay⟩
  · rintro (hxCut | hxOutside)
    · rcases hxCut with ⟨hxX, y, hyx⟩
      refine ⟨incoming x, ⟨?_, ?_⟩, rfl⟩
      · exact Or.inr ⟨x, ⟨hxX, y, hyx⟩, rfl⟩
      · rintro ⟨b, hb⟩
        have hb' := mem_edge_iff.1 hb
        have hrole := congrArg Prod.snd hb'.2.1
        simp [tailCopy, project, hxX, incoming, outgoing] at hrole
    · rcases hxOutside with ⟨hxC, hxX, hxNoOut⟩
      refine ⟨plain x, ⟨?_, ?_⟩, rfl⟩
      · exact Or.inl (Or.inl ⟨x, ⟨hxC, hxX⟩, rfl⟩)
      · rintro ⟨b, hb⟩
        exact hxNoOut ⟨project b, (mem_edge_iff.1 hb).1⟩

theorem edge_biUnique {E : Set (V × V)} {X : Set V}
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) :
    Relator.BiUnique (fun a b ↦ (a, b) ∈ edge E X) := by
  constructor
  · intro a b c hac hbc
    have hac' := mem_edge_iff.1 hac
    have hbc' := mem_edge_iff.1 hbc
    have hab : project a = project b := hE.1 hac'.1 hbc'.1
    rw [hac'.2.1, hbc'.2.1]
    exact congrArg (tailCopy X) hab
  · intro a b c hab hac
    have hab' := mem_edge_iff.1 hab
    have hac' := mem_edge_iff.1 hac
    have hbc : project b = project c := hE.2 hab'.1 hac'.1
    rw [hab'.2.2, hac'.2.2]
    exact congrArg (headCopy X) hbc

/-- An internal vertex of the split relation is necessarily a plain copy
outside `X`.  This is the local fact which makes projection injective on
every split component. -/
theorem internal_eq_plain {E : Set (V × V)} {X : Set V}
    {a b c : Vertex V} (hab : (a, b) ∈ edge E X)
    (hbc : (b, c) ∈ edge E X) : b = plain (project b) := by
  have hab' := mem_edge_iff.1 hab
  have hbc' := mem_edge_iff.1 hbc
  have heq : headCopy X (project b) = tailCopy X (project b) := by
    rw [← hab'.2.2, ← hbc'.2.1]
  have hbX : project b ∉ X := by
    intro hbX
    have hrole := congrArg Prod.snd heq
    simp [headCopy, tailCopy, hbX, incoming, outgoing] at hrole
  simpa [tailCopy, hbX] using hbc'.2.1

theorem cycle_exists_next_eq (K : DirectedCycle (Vertex V))
    (i : Fin K.length) : ∃ j, K.next j = i := by
  by_cases hi : i.1 = 0
  · let j : Fin K.length :=
      ⟨K.length - 1, Nat.sub_lt K.positive (by omega)⟩
    refine ⟨j, Fin.ext ?_⟩
    simp [DirectedCycle.next, j, Nat.sub_add_cancel K.positive, hi]
  · have hiOne : 1 ≤ i.1 := Nat.one_le_iff_ne_zero.mpr hi
    let j : Fin K.length := ⟨i.1 - 1, by omega⟩
    refine ⟨j, Fin.ext ?_⟩
    simp [DirectedCycle.next, j, Nat.sub_add_cancel hiOne,
      Nat.mod_eq_of_lt i.2]

/-- Splitting endpoint roles creates no directed cycle. -/
theorem not_containsDirectedCycle {E : Set (V × V)} {X : Set V}
    (hE : ¬ ContainsDirectedCycle E) :
    ¬ ContainsDirectedCycle (edge E X) := by
  rintro ⟨K, hK⟩
  have hplain (i : Fin K.length) :
      K.vertex i = plain (project (K.vertex i)) := by
    obtain ⟨j, hj⟩ := cycle_exists_next_eq K i
    have hin := hK ⟨j, rfl⟩
    rw [hj] at hin
    exact internal_eq_plain hin (hK ⟨i, rfl⟩)
  let P : DirectedCycle V := {
    length := K.length
    positive := K.positive
    vertex := fun i ↦ project (K.vertex i)
    injective := by
      intro i j hij
      apply K.injective
      rw [hplain i, hplain j]
      exact congrArg plain hij }
  apply hE
  refine ⟨P, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (mem_edge_iff.1 (hK ⟨i, rfl⟩)).1

/-- A directed ray in the split relation would project, after its first
vertex, to a directed ray in the original relation. -/
theorem not_containsDirectedRay {E : Set (V × V)} {X : Set V}
    (hE : ¬ ContainsDirectedRay E) :
    ¬ ContainsDirectedRay (edge E X) := by
  rintro ⟨R, hR⟩
  let P : DirectedRay V := {
    vertex := fun n ↦ project (R.vertex (n + 1))
    injective := by
      intro m n hmn
      have hmPlain : R.vertex (m + 1) = plain (project (R.vertex (m + 1))) :=
        internal_eq_plain (hR ⟨m, rfl⟩) (hR ⟨m + 1, rfl⟩)
      have hnPlain : R.vertex (n + 1) = plain (project (R.vertex (n + 1))) :=
        internal_eq_plain (hR ⟨n, rfl⟩) (hR ⟨n + 1, rfl⟩)
      have hvertices : R.vertex (m + 1) = R.vertex (n + 1) := by
        rw [hmPlain, hnPlain]
        exact congrArg plain hmn
      exact Nat.add_right_cancel (R.injective hvertices) }
  apply hE
  refine ⟨P, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (mem_edge_iff.1 (hR ⟨n + 1, rfl⟩)).1

/-- A reverse ray in the split relation projects, after its first vertex,
to a reverse ray in the original relation. -/
theorem not_containsReverseDirectedRay {E : Set (V × V)} {X : Set V}
    (hE : ¬ ContainsReverseDirectedRay E) :
    ¬ ContainsReverseDirectedRay (edge E X) := by
  rintro ⟨R, hR⟩
  let P : DirectedRay V := {
    vertex := fun n ↦ project (R.vertex (n + 1))
    injective := by
      intro m n hmn
      have hmPlain : R.vertex (m + 1) = plain (project (R.vertex (m + 1))) :=
        internal_eq_plain (hR (m + 1)) (hR m)
      have hnPlain : R.vertex (n + 1) = plain (project (R.vertex (n + 1))) :=
        internal_eq_plain (hR (n + 1)) (hR n)
      have hvertices : R.vertex (m + 1) = R.vertex (n + 1) := by
        rw [hmPlain, hnPlain]
        exact congrArg plain hmn
      exact Nat.add_right_cancel (R.injective hvertices) }
  apply hE
  refine ⟨P, ?_⟩
  intro n
  exact (mem_edge_iff.1 (hR (n + 1))).1

end CutSplit

theorem outsideFamilyEdges_not_containsDirectedRay
    {W : Set Gamma.DPath} {X : Set V}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    ¬ ContainsDirectedRay (outsideFamilyEdges W X) := by
  rintro ⟨R, hR⟩
  exact Alternating.familyEdges_not_containsDirectedRay hW hfinite
    ⟨R, hR.trans (outsideFamilyEdges_subset W X)⟩

theorem outsideFamilyEdges_not_containsReverseDirectedRay
    {W : Set Gamma.DPath} {X : Set V} (hW : Gamma.IsWarp W) :
    ¬ ContainsReverseDirectedRay (outsideFamilyEdges W X) := by
  rintro ⟨R, hR⟩
  exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
    hW ⟨R, fun n ↦ (hR n).1⟩

theorem outsideFamilyEdges_not_containsDirectedCycle
    {W : Set Gamma.DPath} {X : Set V} (hW : Gamma.IsWarp W) :
    ¬ ContainsDirectedCycle (outsideFamilyEdges W X) := by
  rintro ⟨K, hK⟩
  exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
    hW ⟨K, hK.trans (outsideFamilyEdges_subset W X)⟩

/-- The literal cut fragments before projection.  Unlike the recombined
outside warp, this family really stops at every incoming occurrence of `X`
and starts anew at every outgoing occurrence. -/
structure OutsideSplitWarp (W : Set Gamma.DPath) (X : Set V) where
  paths : Set (CutSplit.web Gamma).DPath
  isWarp : (CutSplit.web Gamma).IsWarp paths
  finiteCharacter : (CutSplit.web Gamma).HasFiniteCharacter paths
  /-- A rank on original vertices which strictly increases on every retained
  edge.  It makes projection of each split fragment visibly injective. -/
  projectDepth : V → ℕ
  projectDepth_step : ∀ {x y}, (x, y) ∈ outsideFamilyEdges W X →
    projectDepth y = projectDepth x + 1
  familyEdges_eq : familyEdges paths =
    CutSplit.edge (outsideFamilyEdges W X) X
  vertexSet_eq : (CutSplit.web Gamma).vertexSet paths =
    CutSplit.carrier (outsideCarrier W X) (outsideFamilyEdges W X) X
  initialSet_eq : (CutSplit.web Gamma).initialSet paths =
    {z | z ∈ CutSplit.carrier (outsideCarrier W X)
        (outsideFamilyEdges W X) X ∧
      ¬ ∃ a, (a, z) ∈ CutSplit.edge (outsideFamilyEdges W X) X}
  terminalFrontier_eq : (CutSplit.web Gamma).terminalFrontier paths =
    {z | z ∈ CutSplit.carrier (outsideCarrier W X)
        (outsideFamilyEdges W X) X ∧
      ¬ ∃ b, (z, b) ∈ CutSplit.edge (outsideFamilyEdges W X) X}

namespace OutsideSplitWarp

variable {W : Set Gamma.DPath} {X : Set V}

/-- Every vertex on a split component belongs to the exact split carrier.
This is the pathwise form of `vertexSet_eq`, convenient when comparing two
occurrences with the same projection. -/
theorem support_subset_carrier (S : OutsideSplitWarp W X)
    {p : (CutSplit.web Gamma).DPath} (hp : p ∈ S.paths) :
    p.support ⊆ CutSplit.carrier (outsideCarrier W X)
      (outsideFamilyEdges W X) X := by
  intro z hz
  rw [← S.vertexSet_eq]
  exact ⟨p, hp, hz⟩

/-- The initial vertex of every split component is a root of the exact split
relation. -/
theorem initial_is_root (S : OutsideSplitWarp W X)
    {p : (CutSplit.web Gamma).DPath} (hp : p ∈ S.paths) :
    p.initial ∈ CutSplit.carrier (outsideCarrier W X)
        (outsideFamilyEdges W X) X ∧
      ¬ ∃ a, (a, p.initial) ∈
        CutSplit.edge (outsideFamilyEdges W X) X := by
  have hmem : p.initial ∈ (CutSplit.web Gamma).initialSet S.paths :=
    ⟨p, hp, rfl⟩
  rw [S.initialSet_eq] at hmem
  exact hmem

/-- A finite terminal of a split component is a sink of the exact split
relation. -/
theorem terminal_is_sink (S : OutsideSplitWarp W X)
    {p : (CutSplit.web Gamma).DPath} (hp : p ∈ S.paths) {z}
    (hz : (CutSplit.web Gamma).terminal? p = some z) :
    z ∈ CutSplit.carrier (outsideCarrier W X)
        (outsideFamilyEdges W X) X ∧
      ¬ ∃ b, (z, b) ∈
        CutSplit.edge (outsideFamilyEdges W X) X := by
  have hmem : z ∈ (CutSplit.web Gamma).terminalFrontier S.paths :=
    ⟨p, hp, hz⟩
  rw [S.terminalFrontier_eq] at hmem
  exact hmem

/-- A cut vertex which occurs with the outgoing role on a split component
is necessarily that component's initial vertex. -/
theorem eq_initial_of_eq_outgoing_of_mem_support
    (S : OutsideSplitWarp W X) {p : (CutSplit.web Gamma).DPath}
    (hp : p ∈ S.paths) {z : FracturedDuplication.Vertex V}
    (hz : z ∈ p.support) (hzX : FracturedDuplication.project z ∈ X)
    (hzout : z = FracturedDuplication.outgoing
      (FracturedDuplication.project z)) : z = p.initial := by
  have hzCarrier := S.support_subset_carrier hp hz
  have hzNoIn : ¬ ∃ a, (a, z) ∈
      CutSplit.edge (outsideFamilyEdges W X) X := by
    rintro ⟨a, ha⟩
    have ha' := CutSplit.mem_edge_iff.1 ha
    have hrole : FracturedDuplication.outgoing
        (FracturedDuplication.project z) =
        FracturedDuplication.incoming (FracturedDuplication.project z) := by
      calc
        FracturedDuplication.outgoing (FracturedDuplication.project z) = z :=
          hzout.symm
        _ = CutSplit.headCopy X (FracturedDuplication.project z) :=
          ha'.2.2
        _ = FracturedDuplication.incoming
            (FracturedDuplication.project z) := by
          simp only [CutSplit.headCopy, if_pos hzX]
    exact FracturedDuplication.outgoing_ne_incoming _ hrole
  have hzInitial : z ∈ (CutSplit.web Gamma).initialSet S.paths := by
    rw [S.initialSet_eq]
    exact ⟨hzCarrier, hzNoIn⟩
  obtain ⟨q, hq, hqInitial⟩ := hzInitial
  have hpq : p = q :=
    Alternating.DWeb.IsWarp.eq_of_mem_support S.isWarp hp hq hz
      (hqInitial ▸ q.initial_mem_support)
  subst q
  exact hqInitial.symm

/-- A cut vertex which occurs with the incoming role on a split component
is necessarily that component's finite terminal. -/
theorem terminal_eq_some_of_eq_incoming_of_mem_support
    (S : OutsideSplitWarp W X) {p : (CutSplit.web Gamma).DPath}
    (hp : p ∈ S.paths) {z : FracturedDuplication.Vertex V}
    (hz : z ∈ p.support) (hzX : FracturedDuplication.project z ∈ X)
    (hzin : z = FracturedDuplication.incoming
      (FracturedDuplication.project z)) :
    (CutSplit.web Gamma).terminal? p = some z := by
  have hzCarrier := S.support_subset_carrier hp hz
  have hzNoOut : ¬ ∃ b, (z, b) ∈
      CutSplit.edge (outsideFamilyEdges W X) X := by
    rintro ⟨b, hb⟩
    have hb' := CutSplit.mem_edge_iff.1 hb
    have hrole : FracturedDuplication.incoming
        (FracturedDuplication.project z) =
        FracturedDuplication.outgoing (FracturedDuplication.project z) := by
      calc
        FracturedDuplication.incoming (FracturedDuplication.project z) = z :=
          hzin.symm
        _ = CutSplit.tailCopy X (FracturedDuplication.project z) :=
          hb'.2.1
        _ = FracturedDuplication.outgoing
            (FracturedDuplication.project z) := by
          simp only [CutSplit.tailCopy, if_pos hzX]
    exact FracturedDuplication.outgoing_ne_incoming _ hrole.symm
  have hzTerminal : z ∈ (CutSplit.web Gamma).terminalFrontier S.paths := by
    rw [S.terminalFrontier_eq]
    exact ⟨hzCarrier, hzNoOut⟩
  obtain ⟨q, hq, hqTerminal⟩ := hzTerminal
  have hpq : p = q :=
    Alternating.DWeb.IsWarp.eq_of_mem_support S.isWarp hp hq hz
      ((CutSplit.web Gamma).terminal_mem_support hqTerminal)
  subst q
  exact hqTerminal

/-- An outgoing cut occurrence on a split component has a genuine edge of
that same component leaving it.  In particular it is not an isolated
component. -/
theorem exists_outgoing_edgeSet_of_eq_outgoing_of_mem_support
    (S : OutsideSplitWarp W X) {p : (CutSplit.web Gamma).DPath}
    (hp : p ∈ S.paths) {z : FracturedDuplication.Vertex V}
    (hz : z ∈ p.support) (hzX : FracturedDuplication.project z ∈ X)
    (hzout : z = FracturedDuplication.outgoing
      (FracturedDuplication.project z)) :
    ∃ b, (z, b) ∈ p.edgeSet := by
  have hzCarrier := S.support_subset_carrier hp hz
  rw [CutSplit.mem_carrier_iff] at hzCarrier
  rcases hzCarrier with hzPlain | hzOutgoing | hzIncoming
  · exact (hzPlain.2.2 hzX).elim
  · obtain ⟨y, hzy⟩ := hzOutgoing.2.2
    let b := CutSplit.headCopy X y
    have hzbSplit : (z, b) ∈
        CutSplit.edge (outsideFamilyEdges W X) X := by
      refine ⟨FracturedDuplication.project z, y, hzy, ?_⟩
      apply Prod.ext
      · exact hzout.trans (by
          simp only [CutSplit.tailCopy, if_pos hzX])
      · rfl
    have hzbFamily : (z, b) ∈ familyEdges S.paths := by
      rw [S.familyEdges_eq]
      exact hzbSplit
    simp only [familyEdges, Set.mem_iUnion] at hzbFamily
    obtain ⟨q, hq, hzbq⟩ := hzbFamily
    have hpq : p = q :=
      Alternating.DWeb.IsWarp.eq_of_mem_support S.isWarp hp hq hz
        (q.edgeSet_subset_support_prod hzbq).1
    subst q
    exact ⟨b, hzbq⟩
  · have hcontra : FracturedDuplication.outgoing
        (FracturedDuplication.project z) =
        FracturedDuplication.incoming (FracturedDuplication.project z) :=
      hzout.symm.trans hzIncoming.1
    exact (FracturedDuplication.outgoing_ne_incoming _ hcontra).elim

/-- An incoming cut occurrence on a split component has a genuine edge of
that same component entering it.  In particular it is not an isolated
component. -/
theorem exists_incoming_edgeSet_of_eq_incoming_of_mem_support
    (S : OutsideSplitWarp W X) {p : (CutSplit.web Gamma).DPath}
    (hp : p ∈ S.paths) {z : FracturedDuplication.Vertex V}
    (hz : z ∈ p.support) (hzX : FracturedDuplication.project z ∈ X)
    (hzin : z = FracturedDuplication.incoming
      (FracturedDuplication.project z)) :
    ∃ a, (a, z) ∈ p.edgeSet := by
  have hzCarrier := S.support_subset_carrier hp hz
  rw [CutSplit.mem_carrier_iff] at hzCarrier
  rcases hzCarrier with hzPlain | hzOutgoing | hzIncoming
  · exact (hzPlain.2.2 hzX).elim
  · have hcontra : FracturedDuplication.outgoing
        (FracturedDuplication.project z) =
        FracturedDuplication.incoming (FracturedDuplication.project z) :=
      hzOutgoing.1.symm.trans hzin
    exact (FracturedDuplication.outgoing_ne_incoming _ hcontra).elim
  · obtain ⟨x, hxz⟩ := hzIncoming.2.2
    let a := CutSplit.tailCopy X x
    have hazSplit : (a, z) ∈
        CutSplit.edge (outsideFamilyEdges W X) X := by
      refine ⟨x, FracturedDuplication.project z, hxz, ?_⟩
      apply Prod.ext
      · rfl
      · exact hzin.trans (by
          simp only [CutSplit.headCopy, if_pos hzX])
    have hazFamily : (a, z) ∈ familyEdges S.paths := by
      rw [S.familyEdges_eq]
      exact hazSplit
    simp only [familyEdges, Set.mem_iUnion] at hazFamily
    obtain ⟨q, hq, hazq⟩ := hazFamily
    have hpq : p = q :=
      Alternating.DWeb.IsWarp.eq_of_mem_support S.isWarp hp hq hz
        (q.edgeSet_subset_support_prod hazq).2
    subst q
    exact ⟨a, hazq⟩

/-- Exact original-vertex source formula for the split fragments. -/
theorem project_initialSet (S : OutsideSplitWarp W X) :
    FracturedDuplication.project ''
        (CutSplit.web Gamma).initialSet S.paths =
      CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
  rw [S.initialSet_eq, CutSplit.project_roots]

/-- Exact original-vertex terminal formula for the split fragments. -/
theorem project_terminalFrontier (S : OutsideSplitWarp W X) :
    FracturedDuplication.project ''
        (CutSplit.web Gamma).terminalFrontier S.paths =
      CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
  rw [S.terminalFrontier_eq, CutSplit.project_sinks]

end OutsideSplitWarp

/-- Construct the genuine split outside family directly from `W` and `X`.
No fractured family, assignment, or boundary certificate is supplied as an
input. -/
theorem exists_outsideSplitWarp (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    Nonempty (OutsideSplitWarp W X) := by
  let E : Set (V × V) := outsideFamilyEdges W X
  let C : Set V := outsideCarrier W X
  let Es : Set (FracturedDuplication.Vertex V ×
      FracturedDuplication.Vertex V) := CutSplit.edge E X
  let Cs : Set (FracturedDuplication.Vertex V) := CutSplit.carrier C E X
  have hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    rintro ⟨x, y⟩ hxy
    exact familyEdges_subset_adj W hxy.1
  have hendpoints : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C := by
    intro e he
    exact outsideFamilyEdges_endpoints W X he
  have hbiunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    constructor
    · intro x y z hxz hyz
      exact (Alternating.IsWarp.familyEdges_leftUnique hW) hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (Alternating.IsWarp.familyEdges_rightUnique hW) hxy.1 hxz.1
  have hcycle : ¬ ContainsDirectedCycle E :=
    outsideFamilyEdges_not_containsDirectedCycle hW
  have hreverse : ¬ ContainsReverseDirectedRay E :=
    outsideFamilyEdges_not_containsReverseDirectedRay hW
  have hnRay : ¬ ContainsDirectedRay E :=
    outsideFamilyEdges_not_containsDirectedRay hW hfinite
  obtain ⟨O₀, hO₀E, _hO₀C⟩ :=
    exists_forwardOrientation_exact E C
      hgraph hendpoints hbiunique hcycle hreverse
  obtain ⟨O, hOE, hOC⟩ :=
    exists_forwardOrientation_exact Es Cs
      (CutSplit.edge_in_graph hgraph)
      (CutSplit.edge_endpoints hendpoints)
      (CutSplit.edge_biUnique hbiunique)
      (CutSplit.not_containsDirectedCycle hcycle)
      (CutSplit.not_containsReverseDirectedRay hreverse)
  have hfiniteSplit :
      (CutSplit.web Gamma).HasFiniteCharacter O.rootPaths :=
    Erdos599.Alternating.RelationDecomposition.DWeb.forwardOrientation_rootPaths_finite_of_noRay
      (CutSplit.web Gamma) O (by
        rw [hOE]
        exact CutSplit.not_containsDirectedRay hnRay)
  refine ⟨{
    paths := O.rootPaths
    isWarp := O.rootPaths_pairwiseDisjoint
    finiteCharacter := hfiniteSplit
    projectDepth := O₀.depth
    projectDepth_step := by
      intro x y hxy
      exact O₀.depth_step (hO₀E.symm ▸ hxy)
    familyEdges_eq := ?_
    vertexSet_eq := ?_
    initialSet_eq := ?_
    terminalFrontier_eq := ?_ }⟩
  · change O.rootPathEdges = CutSplit.edge (outsideFamilyEdges W X) X
    exact O.rootPathEdges_eq.trans hOE
  · rw [PathFilterComponents.ForwardOrientation.vertexSet_rootPaths
      (CutSplit.web Gamma) O, hOC]
  · rw [CutOrientation.initialSet_rootPaths_eq_noIncoming
      (CutSplit.web Gamma) O, hOC, hOE]
  · rw [CutOrientation.terminalFrontier_rootPaths_eq_noOutgoing
      (CutSplit.web Gamma) O, hOC, hOE]

/-- The fully constructed honest recombination of `W ↾ X`. -/
structure OutsideEdgeWarp (W : Set Gamma.DPath) (X : Set V) where
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  finiteCharacter : Gamma.HasFiniteCharacter paths
  familyEdges_eq : familyEdges paths = outsideFamilyEdges W X
  vertexSet_eq : Gamma.vertexSet paths = outsideCarrier W X
  initialSet_eq : Gamma.initialSet paths =
    {x | x ∈ outsideCarrier W X ∧
      ¬ ∃ y, (y, x) ∈ outsideFamilyEdges W X}
  terminalFrontier_eq : Gamma.terminalFrontier paths =
    {x | x ∈ outsideCarrier W X ∧
      ¬ ∃ y, (x, y) ∈ outsideFamilyEdges W X}

namespace OutsideEdgeWarp

/-- The recombined outside family, viewed as a fractured warp.  Its path
family is already honest, so the permitted-intersection clause is vacuous. -/
def fractured {W : Set Gamma.DPath} {X : Set V}
    (C : OutsideEdgeWarp W X) : FracturedWarp Gamma where
  paths := C.paths
  edgeWarp := C.paths
  edgeWarp_isWarp := C.isWarp
  same_edges := rfl
  allowed_intersection := by
    intro p hp q hq hpq hmeet
    exact (hmeet (C.isWarp hp hq hpq)).elim

@[simp] theorem fractured_paths {W : Set Gamma.DPath} {X : Set V}
    (C : OutsideEdgeWarp W X) : C.fractured.paths = C.paths := rfl

@[simp] theorem fractured_edgeWarp {W : Set Gamma.DPath} {X : Set V}
    (C : OutsideEdgeWarp W X) : C.fractured.edgeWarp = C.paths := rfl

end OutsideEdgeWarp

/-- Decompose the literal outside-edge relation into finite root orbits.
No path family is supplied as an assumption. -/
theorem exists_outsideEdgeWarp (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    Nonempty (OutsideEdgeWarp W X) := by
  let E : Set (V × V) := outsideFamilyEdges W X
  let C : Set V := outsideCarrier W X
  have hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    rintro ⟨x, y⟩ hxy
    have hxyW : (x, y) ∈ familyEdges W := hxy.1
    simp only [familyEdges, Set.mem_iUnion] at hxyW
    rcases hxyW with ⟨p, hpW, hpedge⟩
    exact p.edgeSet_subset_adj hpedge
  have hendpoints : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C := by
    intro e he
    exact outsideFamilyEdges_endpoints W X he
  have hbiunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    constructor
    · intro x y z hxz hyz
      exact (Alternating.IsWarp.familyEdges_leftUnique hW) hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (Alternating.IsWarp.familyEdges_rightUnique hW) hxy.1 hxz.1
  have hcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨K, hK⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
      hW ⟨K, hK.trans (fun _ he ↦ he.1)⟩
  have hreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      hW ⟨R, fun n ↦ (hR n).1⟩
  have hnRay : ¬ ContainsDirectedRay E := by
    rintro ⟨R, hR⟩
    exact Alternating.familyEdges_not_containsDirectedRay hW hfinite
      ⟨R, hR.trans (outsideFamilyEdges_subset W X)⟩
  obtain ⟨O, hOE, hOC⟩ :=
    exists_forwardOrientation_exact
      E C hgraph hendpoints hbiunique hcycle hreverse
  have hrootFinite : Gamma.HasFiniteCharacter O.rootPaths :=
    Erdos599.Alternating.RelationDecomposition.DWeb.forwardOrientation_rootPaths_finite_of_noRay
      Gamma O (by
      rw [hOE]
      exact hnRay)
  refine ⟨{
    paths := O.rootPaths
    isWarp := O.rootPaths_pairwiseDisjoint
    finiteCharacter := hrootFinite
    familyEdges_eq := ?_
    vertexSet_eq := ?_
    initialSet_eq := ?_
    terminalFrontier_eq := ?_ }⟩
  · change O.rootPathEdges = outsideFamilyEdges W X
    exact O.rootPathEdges_eq.trans hOE
  · rw [PathFilterComponents.ForwardOrientation.vertexSet_rootPaths Gamma O,
      hOC]
  · rw [CutOrientation.initialSet_rootPaths_eq_noIncoming Gamma O,
      hOC, hOE]
  · rw [CutOrientation.terminalFrontier_rootPaths_eq_noOutgoing Gamma O,
      hOC, hOE]

/-- Construct both presentations of the cut relation: the literal split
fragments and their honest recombination.  They have definitionally matching
certified edge sets through their two `familyEdges_eq` fields. -/
theorem exists_outsideSplitAndEdgeWarp (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    ∃ S : OutsideSplitWarp W X, ∃ C : OutsideEdgeWarp W X,
      (fun e : FracturedDuplication.Vertex V ×
          FracturedDuplication.Vertex V ↦
        (FracturedDuplication.project e.1,
          FracturedDuplication.project e.2)) '' familyEdges S.paths =
        familyEdges C.paths := by
  obtain ⟨S⟩ := exists_outsideSplitWarp W X hW hfinite
  obtain ⟨C⟩ := exists_outsideEdgeWarp W X hW hfinite
  refine ⟨S, C, ?_⟩
  rw [S.familyEdges_eq, CutSplit.project_edge_image, C.familyEdges_eq]

/-! ## The exact boundary facts of a cut -/

/-- The literal hole family `W ⇂ X`, together with the exact carrier and
endpoint formulas needed later.  Its `edgeWarp` is only the honest witness
required by `FracturedWarp`; all assignment statements below deliberately use
`holes.paths`.

The preceding theorem constructs the honest filtered-edge witness.  The
remaining path-level construction is the canonical splitting of every member
of `W` at successive visits to `X`; keeping that datum separate prevents an
accidental replacement of the holes by their recombination. -/
structure OutsideFracturedWarp (W : Set Gamma.DPath) (X : Set V) where
  holes : FracturedWarp Gamma
  finiteCharacter : Gamma.HasFiniteCharacter holes.paths
  /-- Finite character of the recombination rules out an infinite tail made
  solely of consecutive holes.  This is the exact extra hypothesis needed
  when the duplicated-vertex assignment is projected and maximal constant
  direction runs are recompressed. -/
  edgeWarpFiniteCharacter : Gamma.HasFiniteCharacter holes.edgeWarp
  familyEdges_eq : familyEdges holes.paths = outsideFamilyEdges W X
  vertexSet_eq : Gamma.vertexSet holes.paths = outsideCarrier W X
  initialSet_eq : Gamma.initialSet holes.paths =
    CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X
  terminalFrontier_eq : Gamma.terminalFrontier holes.paths =
    CutSplit.terminalVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X

namespace OutsideFracturedWarp

variable {W : Set Gamma.DPath} {X : Set V}

/-- The certified recombination of the literal holes has the same filtered
edge relation. -/
theorem edgeWarp_familyEdges (F : OutsideFracturedWarp W X) :
    familyEdges F.holes.edgeWarp = outsideFamilyEdges W X := by
  rw [← F.holes.same_edges, F.familyEdges_eq]

end OutsideFracturedWarp

/-! ## Colour changes after projecting the duplicated assignment -/

/-- If forward edges cannot contain a directed ray and backward edges cannot
contain a reverse directed ray, an injective two-colour stream must change
colour arbitrarily far out.  This is precisely the hypothesis expected by
`RunCompressor.InfiniteInput.toInfiniteRunWalk`.

In the duplicated-vertex proof of Remark 4.20, contracted connector steps are
deleted first.  A hypothetical eventually-forward projected tail would be a
ray in the recombined outside warp; an eventually-backward tail would be a
reverse ray in the reference warp. -/
theorem colours_change_of_no_rays
    {Eforward Ebackward : Set (V × V)}
    (hforwardRay : ¬ ContainsDirectedRay Eforward)
    (hbackwardRay : ¬ ContainsReverseDirectedRay Ebackward)
    (vertex : ℕ → V) (hinjective : Function.Injective vertex)
    (colour : ℕ → Direction)
    (hforward : ∀ n, colour n = .forward →
      (vertex n, vertex (n + 1)) ∈ Eforward)
    (hbackward : ∀ n, colour n = .backward →
      (vertex (n + 1), vertex n) ∈ Ebackward) :
  ∀ n, ∃ m, n < m ∧ colour m ≠ colour n := by
  by_contra hchange
  push Not at hchange
  obtain ⟨n, hn⟩ := hchange
  let R : DirectedRay V := {
    vertex := fun k ↦ vertex (n + 1 + k)
    injective := fun _ _ h ↦ Nat.add_left_cancel (hinjective h) }
  cases hdir : colour (n + 1) with
  | forward =>
      apply hforwardRay
      refine ⟨R, ?_⟩
      rintro e ⟨k, rfl⟩
      have hc : colour (n + 1 + k) = .forward := by
        exact (hn (n + 1 + k) (by omega)).trans
          ((hn (n + 1) (by omega)).symm.trans hdir)
      simpa only [R, Nat.add_assoc] using hforward (n + 1 + k) hc
  | backward =>
      apply hbackwardRay
      refine ⟨R, ?_⟩
      intro k
      have hc : colour (n + 1 + k) = .backward := by
        exact (hn (n + 1 + k) (by omega)).trans
          ((hn (n + 1) (by omega)).symm.trans hdir)
      simpa only [R, Nat.add_assoc] using hbackward (n + 1 + k) hc

/-- Finite character of the recombined holes is exactly what excludes the
eventually-forward counterexample to fractured assignment; ordinary warp
disjointness excludes an eventually-backward reference tail. -/
theorem OutsideFracturedWarp.projectedColours_change
    {W : Set Gamma.DPath} {X : Set V}
    (F : OutsideFracturedWarp W X) (hY : Gamma.IsWarp Y)
    (vertex : ℕ → V) (hinjective : Function.Injective vertex)
    (colour : ℕ → Direction)
    (hforward : ∀ n, colour n = .forward →
      (vertex n, vertex (n + 1)) ∈ familyEdges F.holes.edgeWarp)
    (hbackward : ∀ n, colour n = .backward →
      (vertex (n + 1), vertex n) ∈ familyEdges Y) :
    ∀ n, ∃ m, n < m ∧ colour m ≠ colour n := by
  apply colours_change_of_no_rays
    (Alternating.familyEdges_not_containsDirectedRay
      F.holes.edgeWarp_isWarp F.edgeWarpFiniteCharacter)
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      hY)
    vertex hinjective colour hforward hbackward

/-- Relation-level boundary data for the outside-edge decomposition.  These
are the statements proved from the slice geometry and closure under the
reference warp; they do not mention a proposed assignment or result
blueprint. -/
structure OutsideCutBoundary (W : Set Gamma.DPath) (X : Set V)
    (before innerRoof outerRoof : Set V) where
  initial_on_reference :
    (CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X ∩
        Gamma.vertexSet Y) ⊆ Gamma.initialSet Y
  terminal_on_reference :
    (CutSplit.terminalVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X ∩
        Gamma.vertexSet Y) ⊆ Gamma.terminalFrontier Y
  reference_initials : Gamma.initialSet Y ⊆
    CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X
  source_location :
    (CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X \
        Gamma.initialSet Y) ⊆ before ∩ innerRoof
  terminal_location :
    (CutSplit.terminalVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X \
        Gamma.vertexSet Y) ⊆ before ∩ outerRoof

namespace OutsideCutBoundary

variable {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}

/-- Boundary alignment for the literal fractured family. -/
theorem fractured_boundaryAligned (F : OutsideFracturedWarp W X)
    (B : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof) :
    BoundaryAligned F.holes.paths Y := by
  constructor
  · rw [F.initialSet_eq]
    exact B.initial_on_reference
  · rw [F.terminalFrontier_eq]
    exact B.terminal_on_reference

/-- Every reference initial is a literal hole initial. -/
theorem fractured_referenceInitials (F : OutsideFracturedWarp W X)
    (B : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof) :
    Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths := by
  rw [F.initialSet_eq]
  exact B.reference_initials

theorem fractured_uncoveredInitial_location (F : OutsideFracturedWarp W X)
    (B : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof) :
    Gamma.initialSet F.holes.paths \ Gamma.initialSet Y ⊆
      before ∩ innerRoof := by
  rw [F.initialSet_eq]
  exact B.source_location

theorem fractured_uncoveredTerminal_location (F : OutsideFracturedWarp W X)
    (B : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof) :
    Gamma.terminalFrontier F.holes.paths \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof := by
  rw [F.terminalFrontier_eq]
  exact B.terminal_location

end OutsideCutBoundary

/-! ## The selected assignment and its closure geometry -/

/-- Source-faithful geometric output of applying Theorem 4.12 to the holes
of `W ↾ X`.  It says literally that a selected assigned trace has no
closed-set vertex except its prescribed endpoint(s), and that it really
uses a vertex outside `X`. -/
structure OutsideAssignment
    {W : Set Gamma.DPath} {X : Set V}
    (F : OutsideFracturedWarp W X) where
  assignment : SimultaneousAssignment F.holes.paths Y
  finite_meets_closure : ∀ s v,
    (assignment.assigned s).terminal? = some v →
      (assignment.assigned s).vertexSet ∩ X ⊆ {s.1, v}
  infinite_meets_closure : ∀ s,
    (assignment.assigned s).IsInfinite →
      (assignment.assigned s).vertexSet ∩ X ⊆ {s.1}
  leaves_closure : ∀ s, ¬ (assignment.assigned s).vertexSet ⊆ X

namespace OutsideAssignment

variable {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
variable {F : OutsideFracturedWarp W X}

/-- The endpoint-intersection form used by `OutsideAssignment` is equivalent
to the interior-disjointness form stored by `AssignmentClosureContext`.  This
constructor lets a projected assignment proved directly by the closing-up
argument enter the cut package without duplicating geometric proofs. -/
def ofAssignmentClosureContext
    (A : SimultaneousAssignment F.holes.paths Y)
    (hA : AssignmentClosureContext A X before innerRoof outerRoof) :
    OutsideAssignment (Y := Y) F where
  assignment := A
  finite_meets_closure := by
    intro s v hterm x hx
    by_contra hxend
    have hxInterior :
        x ∈ hammockInterior s.1 (.vertex v) (A.assigned s) := by
      refine ⟨hx.1, ?_⟩
      simpa [hammockEndpoints] using hxend
    exact Set.disjoint_left.1 (hA.interior_disjoint_finite s v hterm)
      hxInterior hx.2
  infinite_meets_closure := by
    intro s hinfinite x hx
    by_contra hxend
    have hxInterior :
        x ∈ hammockInterior s.1 .infinity (A.assigned s) := by
      refine ⟨hx.1, ?_⟩
      simpa [hammockEndpoints] using hxend
    exact Set.disjoint_left.1 (hA.interior_disjoint_infinite s hinfinite)
      hxInterior hx.2
  leaves_closure := hA.outside

/-- The cut boundary and the literal hole-intersection formula discharge all
five fields of `AssignmentClosureContext`. -/
theorem assignmentClosureContext
    (B : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (A : OutsideAssignment (Y := Y) F) :
    AssignmentClosureContext A.assignment X before innerRoof outerRoof := by
  refine {
    eligible_finite := ?_
    eligible_infinite := ?_
    interior_disjoint_finite := ?_
    interior_disjoint_infinite := ?_
    outside := A.leaves_closure }
  · intro s v hterm
    refine ⟨B.fractured_uncoveredInitial_location F s.property, ?_⟩
    exact B.fractured_uncoveredTerminal_location F
      (A.assignment.finite_terminal_mem s hterm)
  · intro s hinfinite
    exact ⟨B.fractured_uncoveredInitial_location F s.property, trivial⟩
  · intro s v hterm
    rw [Set.disjoint_left]
    intro x hxInterior hxX
    have hxMeet : x ∈ (A.assignment.assigned s).vertexSet ∩ X :=
      ⟨hxInterior.1, hxX⟩
    have hxEndpoints := A.finite_meets_closure s v hterm hxMeet
    exact hxInterior.2 (by simpa [hammockEndpoints] using hxEndpoints)
  · intro s hinfinite
    rw [Set.disjoint_left]
    intro x hxInterior hxX
    have hxMeet : x ∈ (A.assignment.assigned s).vertexSet ∩ X :=
      ⟨hxInterior.1, hxX⟩
    have hxEndpoint := A.infinite_meets_closure s hinfinite hxMeet
    exact hxInterior.2 (by simpa [hammockEndpoints] using hxEndpoint)

end OutsideAssignment

/-! ## A scheduler-ready cut package -/

/-- The exact cut-dependent object constructed after the closing set is
known: the literal holes with their recombination certificate, their boundary
data, and the one selected outside assignment.  This record contains neither
a replacement blueprint nor any of the conclusions of Assertion 9.31. -/
structure OutsideCutConstruction (W : Set Gamma.DPath) (X : Set V)
    (before innerRoof outerRoof : Set V) where
  outside : OutsideFracturedWarp W X
  boundary : OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof
  assigned : OutsideAssignment (Y := Y) outside

namespace OutsideCutConstruction

variable {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}

def fractured
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    FracturedWarp Gamma :=
  D.outside.holes

theorem boundaryAligned
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    BoundaryAligned D.fractured.paths Y := by
  simpa [fractured] using D.boundary.fractured_boundaryAligned D.outside

theorem finiteCharacter
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    Gamma.HasFiniteCharacter D.fractured.paths := by
  change Gamma.HasFiniteCharacter D.outside.holes.paths
  exact D.outside.finiteCharacter

theorem edgeWarpFiniteCharacter
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    Gamma.HasFiniteCharacter D.fractured.edgeWarp := by
  change Gamma.HasFiniteCharacter D.outside.holes.edgeWarp
  exact D.outside.edgeWarpFiniteCharacter

theorem referenceInitials
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    Gamma.initialSet Y ⊆ Gamma.initialSet D.fractured.paths := by
  simpa [fractured] using
    D.boundary.fractured_referenceInitials D.outside

def assignment
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    SimultaneousAssignment D.fractured.paths Y := by
  change SimultaneousAssignment D.outside.holes.paths Y
  exact D.assigned.assignment

theorem assignmentClosure
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    AssignmentClosureContext D.assignment X before innerRoof outerRoof := by
  simpa [assignment, fractured] using
    D.assigned.assignmentClosureContext D.boundary

end OutsideCutConstruction

end LinkageBlueprint
end Blueprint
end Erdos599
