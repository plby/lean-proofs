/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintReplacement
import ErdosProblems.Erdos599.LadderLemma76

/-!
# Retaining the club-stage geometry used by the half-way construction

The terminal scheduler in Section 9 does not merely use a triple of sets.
At a successor transaction it also needs the two ladder stages, the
cumulative closed set below the later stage, the strict and ordinary roofs
of the later frontier, the outside-fragment construction, and the concrete
inside-edge union.  Erasing these data makes Assertions 9.22--9.31
impossible to instantiate later.

This file packages those source-level data without postulating either of the
two provider propositions consumed by `GlobalBlueprintReplacement`.  A
`ClubStageSeedSystem` contains the actual closure seed and fractured family
as functions of the current blueprint and closing set.  A
`ClubStageUnionSystem` contains the actual inside relation, carrier, rank,
and boundary facts.  The theorems at the end construct, respectively,
`ClosedFracturedReplacementSeedProvider` and
`WholeFamilyUnionGeometryCompiler`, and then invoke the checked global
transaction compiler.

The old and new slices, the two roofs, the eventual persistent set, the
closed stage, and the set closed before the new stage are definitions, not
fields.  In particular the resulting providers cannot silently choose
incompatible versions of those sets.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-! ## The retained club-stage configuration -/

/-- The union of the closed sets constructed strictly before a ladder
stage.  This is the formal `Z_{< beta}` occurring in Definition 9.20. -/
def closedBefore (closedStage : Ladder.Stage theta -> Set V)
    (beta : Ladder.Stage theta) : Set V :=
  {x | exists alpha : Ladder.Stage theta,
    alpha < beta ∧ x ∈ closedStage alpha}

@[simp] theorem mem_closedBefore
    {closedStage : Ladder.Stage theta -> Set V}
    {beta : Ladder.Stage theta} {x : V} :
    x ∈ closedBefore closedStage beta ↔
      exists alpha : Ladder.Stage theta,
        alpha < beta ∧ x ∈ closedStage alpha :=
  Iff.rfl

/-- One pair of club stages together with the increasing closed-stage
family used by the Section 9 closing-up construction.

`kappa` is the blueprint/assignment capacity, while `theta` is the length
of the ladder.  Keeping them separate matches the source use of a
`lambda^+`-ladder while all one-step constructions have size at most
`lambda`. -/
structure ClubStageGeometry
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (kappa theta : Cardinal.{u}) where
  ladder : Gamma.KappaLadder theta
  legal : ladder.IsLegal
  normalized : Gamma.IsNormalized
  club : Set (Ladder.Stage theta)
  club_isClub : Stationary.IsClubBelow theta club
  club_avoids_phi : Disjoint club ladder.phi
  oldStage : Ladder.Stage theta
  newStage : Ladder.Stage theta
  old_mem_club : oldStage ∈ club
  new_mem_club : newStage ∈ club
  old_lt_new : oldStage < newStage
  closedStage : Ladder.Stage theta -> Set V
  closedStage_mono : ∀ {a b}, a ≤ b -> closedStage a ⊆ closedStage b
  before_card : #(closedBefore closedStage newStage) ≤ kappa
  capacity_infinite : aleph0 ≤ kappa

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Y kappa theta)

/-- The slice at which the incoming blueprint lives. -/
abbrev oldSlice : Set V := C.ladder.frontier C.oldStage

/-- The later slice at which the replacement blueprint is certified. -/
abbrev newSlice : Set V := C.ladder.frontier C.newStage

/-- The strict roof in the hammock eligibility condition. -/
abbrev innerRoof : Set V := Gamma.strictRoof C.newSlice

/-- The ordinary roof which contains all objects of the transaction. -/
abbrev outerRoof : Set V := Gamma.roof C.newSlice

/-- The stage of the global closed set available to the transaction. -/
abbrev closedSet : Set V := C.closedStage C.newStage

/-- The cumulative closed set strictly before the later stage. -/
abbrev before : Set V := closedBefore C.closedStage C.newStage

/-- The vertices which survive on every sufficiently late ladder frontier,
the set called `T_{lambda^+}` in (9.19). -/
abbrev persistent : Set V :=
  C.ladder.limitRoof \ C.ladder.limitStrictRoof

/-- Earlier closed stages really are contained in the closed set at the
later stage. -/
theorem before_subset_closedSet : C.before ⊆ C.closedSet := by
  rintro x ⟨a, ha, hxa⟩
  exact C.closedStage_mono ha.le hxa

/-- Both selected club stages have unhindered quotient-stage webs.  This is
the direct use of legality and Lemma 7.6: a hindered maximal rung would put
the stage in `phi`, contradicting club avoidance. -/
theorem stageWeb_isUnhindered {a : Ladder.Stage theta}
    (ha : a ∈ C.club) : (C.ladder.stageWeb a).IsUnhindered := by
  intro hhindered
  obtain ⟨W, hW⟩ := hhindered
  have hrung :
      (C.ladder.stageWeb a).IsHindrance (C.ladder.rung a) :=
    C.legal.hinderedStagesHaveHindranceRungs a
      (fun hstage => hstage ⟨W, hW⟩)
  have hphi : a ∈ C.ladder.phi :=
    C.ladder.phiHindrance_subset_phi C.normalized C.legal hrung
  exact Set.disjoint_left.1 C.club_avoids_phi ha hphi

theorem oldStage_isUnhindered :
    (C.ladder.stageWeb C.oldStage).IsUnhindered :=
  C.stageWeb_isUnhindered C.old_mem_club

theorem newStage_isUnhindered :
    (C.ladder.stageWeb C.newStage).IsUnhindered :=
  C.stageWeb_isUnhindered C.new_mem_club

end ClubStageGeometry

/-! ## Raw seed data -/

/-- Source data for Assertions 9.22--9.25 at one retained club-stage pair.

Unlike `ClosedFracturedReplacementSeed`, this is a system of concrete
choices.  In particular `initialSeed` and `fractured` are functions of the
current blueprint and scheduled terminal, and all four closure sets are the
fixed ladder-derived definitions above. -/
structure ClubStageSeedSystem
    (C : ClubStageGeometry Gamma Y kappa theta) where
  Preserves : FinitePath Gamma.graph -> Prop
  target_paths : ∀ v ∈ C.oldSlice ∩ C.outerRoof,
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ C.newSlice ∧
        p.support ⊆ C.outerRoof ∧ Preserves p
  reference_isWarp : Gamma.IsWarp Y
  reference_finite : Gamma.HasFiniteCharacter Y
  reference_in_roof : ∀ p ∈ Y, p.support ⊆ C.outerRoof
  safe_in_roof : EligibleHammocksContainedInRoof Gamma Y
    C.before C.innerRoof C.outerRoof
  initialSeed : LinkageBlueprint Gamma Y kappa -> V -> Set V
  initial_card : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent ->
      C.persistent ⊆ C.newSlice -> u ∈ W.realPart.terminals ->
        #(initialSeed W u) ≤ kappa
  initial_in_roof : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent ->
      C.persistent ⊆ C.newSlice -> u ∈ W.realPart.terminals ->
        initialSeed W u ⊆ C.outerRoof
  fractured : LinkageBlueprint Gamma Y kappa -> V ->
    Set V -> FracturedWarp Gamma
  boundary_aligned : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (X : Set V), BoundaryAligned (fractured W u X).paths Y
  finite_character : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (X : Set V),
    Gamma.HasFiniteCharacter (fractured W u X).paths
  recombined_finite_character :
    ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V) (X : Set V),
      Gamma.HasFiniteCharacter (fractured W u X).edgeWarp
  reference_initials : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (X : Set V),
    Gamma.initialSet Y ⊆ Gamma.initialSet (fractured W u X).paths
  assignment : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (X : Set V),
    SimultaneousAssignment (fractured W u X).paths Y
  assignment_closure : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (X : Set V), AssignmentClosureContext (assignment W u X)
        X C.before C.innerRoof C.outerRoof

namespace ClubStageSeedSystem

variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- Build the actual global-replacement seed for one scheduler request. -/
def seed (S : ClubStageSeedSystem C)
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hu : u ∈ W.realPart.terminals) :
    ClosedFracturedReplacementSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa) C.persistent where
  before := C.before
  innerRoof := C.innerRoof
  outerRoof := C.outerRoof
  targetSlice := C.oldSlice
  -- The closing-up paths stop at the later ladder frontier.  Requiring
  -- their terminal to be in the ambient web target would contradict the
  -- simultaneous requirement that their whole support remain in this roof.
  targetSide := C.newSlice
  initialSeed := S.initialSeed W u
  Preserves := S.Preserves
  target_paths := S.target_paths
  reference_isWarp := S.reference_isWarp
  reference_in_roof := S.reference_in_roof
  safe_in_roof := S.safe_in_roof
  kappa_infinite := C.capacity_infinite
  before_card := C.before_card
  initial_card := S.initial_card W u hW hpersistent hu
  initial_in_roof := S.initial_in_roof W u hW hpersistent hu
  fractured := S.fractured W u
  boundary_aligned := S.boundary_aligned W u
  finite_character := S.finite_character W u
  recombined_finite_character := S.recombined_finite_character W u
  reference_initials := S.reference_initials W u
  assignment := S.assignment W u
  assignment_closure := S.assignment_closure W u

/-- The retained source geometry constructs the exact seed provider
consumed by the global replacement theorem. -/
theorem seedProvider (S : ClubStageSeedSystem C) :
    ClosedFracturedReplacementSeedProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent Gamma.target := by
  intro W u hW hpersistent hu
  exact ⟨S.seed W u hW hpersistent hu⟩

end ClubStageSeedSystem

/-! ## Raw inside-union geometry -/

/-- The concrete relation data retained from the Section 9 splice.

There is no result blueprint, orientation, splice relation, or
`WholeFamilyUnionGeometry` field here.  Those objects are constructed by
the conversion below and by `GlobalBlueprintReplacement`. -/
structure ClubStageUnionData
    (C : ClubStageGeometry Gamma Y kappa theta)
    (W : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (A : SimultaneousAssignment Zf.paths Y) (u : V) where
  inside : Set (V × V)
  carrier : Set V
  inside_in_graph : inside ⊆
    {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2}
  inside_endpoints : ∀ e ∈ inside,
    e.1 ∈ carrier ∧ e.2 ∈ carrier
  assigned_endpoints : ∀ e ∈ assignedFiniteEdges A,
    e.1 ∈ carrier ∧ e.2 ∈ carrier
  inside_biunique : Relator.BiUnique (fun x y => (x, y) ∈ inside)
  cross_in : ∀ {x y z}, (x, z) ∈ inside ->
    (y, z) ∈ assignedFiniteEdges A -> x = y
  cross_out : ∀ {x y z}, (x, y) ∈ inside ->
    (x, z) ∈ assignedFiniteEdges A -> y = z
  rank : V -> Nat
  inside_rank : ∀ {x y}, (x, y) ∈ inside -> rank x < rank y
  assigned_rank : ∀ {x y},
    (x, y) ∈ assignedFiniteEdges A -> rank x < rank y
  infinite_sources_sink : assignedInfiniteSources A ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ inside ∪ assignedFiniteEdges A}
  sink_boundary :
    {x | x ∈ carrier ∧ ¬ ∃ y,
      (x, y) ∈ inside ∪ assignedFiniteEdges A} ⊆
      assignedInfiniteSources A ∪ C.newSlice
  carrier_roofed : carrier ⊆ C.outerRoof
  covers_source : Gamma.source ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y,
      (y, x) ∈ inside ∪ assignedFiniteEdges A} ∪
      Gamma.initialSet
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y carrier)
  carrier_closed : carrier ⊆ C.closedSet
  card_carrier : #carrier ≤ kappa
  every_relation_ray_strong :
    ∀ r : Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ inside ∪ assignedFiniteEdges A ->
        (strongEdgeIndices r).Infinite
  stable_boundary :
    {x | x ∈ carrier ∧ ¬ ∃ y,
      (x, y) ∈ inside ∪ assignedFiniteEdges A} ∩ C.newSlice ⊆
      C.persistent
  old_real_vertices : W.realPart.vertices ⊆ carrier
  old_real_edges : W.realPart.edges ⊆
    relationRealEdges (Gamma := Gamma)
      (inside ∪ assignedFiniteEdges A)
  old_vertices_accounted : W.vertexSet ⊆
    ({x | x ∈ carrier ∧ ¬ ∃ y,
      (x, y) ∈ inside ∪ assignedFiniteEdges A} ∩ W.terminalSet) ∪
      {x | ∃ y,
        (x, y) ∈ W.familyGraph.edges ∩
          (inside ∪ assignedFiniteEdges A)} ∪
        relationCompletedRealVertices (Gamma := Gamma)
          (inside ∪ assignedFiniteEdges A) carrier Gamma.target
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = u
  target_path_finish : target_path.finish ∈ Gamma.target
  target_path_vertices : target_path.support ⊆ carrier
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma)
      (inside ∪ assignedFiniteEdges A)
  preserves_other_real_terminals :
    W.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma)
        (inside ∪ assignedFiniteEdges A) carrier

namespace ClubStageUnionData

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {W : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma}
variable {A : SimultaneousAssignment Zf.paths Y} {u : V}

/-- Package the raw sink/source/persistence statements as the boundary
record used by the generic relation compiler. -/
def boundary (D : ClubStageUnionData C W A u) :
    WholeFamilySpliceBoundary W A u C.newSlice C.closedSet
      C.persistent Gamma.target
      (D.inside ∪ assignedFiniteEdges A) D.carrier where
  infinite_sources_sink := D.infinite_sources_sink
  sink_boundary := D.sink_boundary
  vertices_roofed := D.carrier_roofed
  covers_source := D.covers_source
  vertices_closed := D.carrier_closed
  card_carrier := D.card_carrier
  every_relation_ray_strong := D.every_relation_ray_strong
  stable_boundary := D.stable_boundary
  old_real_vertices := D.old_real_vertices
  old_real_edges := D.old_real_edges
  old_vertices_accounted := D.old_vertices_accounted
  target_path := D.target_path
  target_path_start := D.target_path_start
  target_path_finish := D.target_path_finish
  target_path_vertices := D.target_path_vertices
  target_path_edges := D.target_path_edges
  preserves_other_real_terminals := D.preserves_other_real_terminals

/-- Construct the exact union-geometry object.  Bi-uniqueness, acyclicity,
and the root-orbit blueprint are still proved downstream from these raw
fields. -/
def toWholeFamilyUnionGeometry (D : ClubStageUnionData C W A u) :
    WholeFamilyUnionGeometry W A u C.newSlice C.closedSet
      C.persistent Gamma.target where
  inside := D.inside
  carrier := D.carrier
  inside_in_graph := D.inside_in_graph
  inside_endpoints := D.inside_endpoints
  assigned_endpoints := D.assigned_endpoints
  inside_biunique := D.inside_biunique
  cross_in := D.cross_in
  cross_out := D.cross_out
  rank := D.rank
  inside_rank := D.inside_rank
  assigned_rank := D.assigned_rank
  boundary := D.boundary

end ClubStageUnionData

/-- A construction of the raw inside-union data for every scheduler
request.  The finite/infinite classification hypotheses are deliberately
absent: they are consequences of the closed seed and are consumed only by
the generic global transaction. -/
def ClubStageUnionSystem
    (C : ClubStageGeometry Gamma Y kappa theta) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent ->
      C.persistent ⊆ C.newSlice -> u ∈ W.realPart.terminals ->
      ∀ (R : ClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) C.persistent)
        (A : SimultaneousAssignment R.fractured.paths Y),
        Nonempty (ClubStageUnionData C W A u)

/-- The raw club-stage union system constructs the exact geometry compiler
consumed by `stable934Compiler_of_globalFracturedSeedAndUnion`. -/
theorem wholeFamilyUnionGeometryCompiler_of_clubStage
    {C : ClubStageGeometry Gamma Y kappa theta}
    (H : ClubStageUnionSystem C) :
    WholeFamilyUnionGeometryCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent Gamma.target := by
  intro W u hW hpersistent hu R A _hfinite _hinfinite
  exact ⟨(H W u hW hpersistent hu R A).some.toWholeFamilyUnionGeometry⟩

/-! ## The checked Section 9 transaction -/

/-- The retained club-stage data discharge both erased providers and hence
give the exact stable successor consumed by the terminal scheduler. -/
theorem stable934Compiler_of_clubStageGeometry
    {C : ClubStageGeometry Gamma Y kappa theta}
    (S : ClubStageSeedSystem C)
    (U : ClubStageUnionSystem C) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      C.newSlice C.closedSet C.persistent Gamma.target := by
  exact stable934Compiler_of_globalFracturedSeedAndUnion
    C.normalized S.reference_isWarp S.reference_finite
    S.seedProvider
    (wholeFamilyUnionGeometryCompiler_of_clubStage U)

end LinkageBlueprint
end Blueprint
end Erdos599
