/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedCanonicalReferenceLift
import ErdosProblems.Erdos599.FracturedAssignmentPeel
import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch

/-!
# Boundary geometry for the canonical fractured/reference lifts

The simultaneous coloured dichotomy is applied only after covered singleton
components have been peeled.  Its forward family is the fixed-role canonical
lift of the active finite fractured members, and its backward family is the
singleton-aware canonical lift of the peeled reference.

The extra hypothesis `NoJunctionOnReference` is applied only to the peeled
`activeReference`: a retained downstairs reference vertex is not
simultaneously an initial and a finite terminal of the fractured family.
Common singleton fractured/reference members are allowed and are removed by
the peel before this hypothesis is used.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedCanonicalBoundary

open Set DirectedPath Alternating
open Alternating.FracturedDuplication
open Alternating.FracturedCanonicalFiniteLift
open Alternating.FracturedCanonicalReferenceLift
open FracturedAssignmentPeel

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- No fracture junction lies on the downstairs reference carrier. -/
def NoJunctionOnReference (Z : FracturedWarp Gamma)
    (Y : Set Gamma.DPath) : Prop :=
  ∀ {x : V}, x ∈ Gamma.vertexSet Y → ¬ IsJunction Z x

/-- If a proper edge of one fractured member enters the initial vertex of
another member, then that head is a genuine fracture junction.  This is the
precise use of the allowed-intersection axiom needed for isolated-reference
avoidance below. -/
theorem junction_of_initial_of_mem_finiteEdge
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hp : (.inl p : Gamma.DPath) ∈ Z.paths) {a b : V}
    (hab : (a, b) ∈ p.edgeSet)
    (hb : b ∈ Gamma.initialSet Z.paths) : IsJunction Z b := by
  rcases hb with ⟨q, hq, hqInitial⟩
  have hpq : (.inl p : Gamma.DPath) ≠ q := by
    intro heq
    subst q
    have hstart : p.start = b := hqInitial
    exact Alternating.FinitePath.target_ne_start_of_mem_edgeSet
      p hab hstart.symm
  have hbP : b ∈ DirectedPath.Path.support (.inl p : Gamma.DPath) :=
    (p.edgeSet_subset_support_prod hab).2
  have hbQ : b ∈ q.support := hqInitial.symm ▸ q.initial_mem_support
  have hmeet : ¬ Disjoint
      (DirectedPath.Path.support (.inl p : Gamma.DPath)) q.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨b, hbP, hbQ⟩
  rcases Z.allowed_intersection hp hq hpq hmeet with
    ⟨_, _, hleft | hright⟩
  · rcases hleft with ⟨t, _hqt, hpInitial, hinter⟩
    have hbt : b = t := by
      have : b ∈ ({t} : Set V) := by
        rw [← hinter]
        exact ⟨hbP, hbQ⟩
      simpa using this
    have hstart : p.start = b := hpInitial.trans hbt.symm
    exact False.elim (Alternating.FinitePath.target_ne_start_of_mem_edgeSet
      p hab hstart.symm)
  · rcases hright with ⟨t, hpt, hqInitial', _hinter⟩
    have htb : t = b := hqInitial'.symm.trans hqInitial
    refine ⟨⟨q, hq, hqInitial⟩, .inl p, hp, ?_⟩
    exact htb ▸ hpt

/-- A reference singleton met by an active fractured member is not one of
the covered singleton owners removed by `activeReference`. -/
theorem trivialPath_mem_activeReference_of_active_support
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    {p : Gamma.DPath} (hp : p ∈ activePaths Z) {x : V}
    (hxp : x ∈ p.support) (hx : x ∈ isolatedVertices Y) :
    Gamma.trivialPath x ∈ activeReference Z Y := by
  refine ⟨hx, ?_⟩
  rintro ⟨⟨a, haSingleton, haeq⟩, _⟩
  have hxa : x = a := by
    have hmem : x ∈ (Gamma.trivialPath a).support := by
      rw [haeq]
      simp [Gamma.support_trivialPath]
    simpa [Gamma.support_trivialPath] using hmem
  subst a
  exact Set.disjoint_left.1
    (activePath_avoids_singletonVertices Z hp) hxp haSingleton

/-- The canonical lifted copy of a retained reference singleton is terminal
at the same outgoing role at which it starts. -/
theorem outgoing_mem_terminalFrontier_canonicalPeeledReferenceLift_of_trivial
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath} {x : V}
    (hx : Gamma.trivialPath x ∈ activeReference Z Y) :
    outgoing x ∈ (web Gamma Z).terminalFrontier
      (liftedReferencePaths Z (activeReference Z Y)) := by
  rw [terminalFrontier_liftedReferencePaths]
  refine ⟨FinitePath.trivial Gamma.graph x, ?_, ?_⟩
  · simpa [DWeb.trivialPath, Path.trivial] using hx
  · simp [referenceTerminalCopy]

/-- Proper forward edges of an interval-safe canonical word avoid every
downstairs isolated reference vertex at both endpoints.  The tail is ruled
out by endpoint purity at the retained outgoing singleton copy.  At the
head, source inclusion plus the fractured allowed-intersection law would
make the vertex a forbidden junction. -/
theorem properForwardImage_endpoints_not_isolated
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y))
    {F : Set (Vertex V × Vertex V)}
    (hF : F ⊆ familyEdges (liftedActiveFinitePaths Z))
    (hpure : ∀ {a b : Vertex V}, (a, b) ∈ F →
      b ∉ (web Gamma Z).initialSet
          (liftedReferencePaths Z (activeReference Z Y)) ∧
        a ∉ (web Gamma Z).terminalFrontier
          (liftedReferencePaths Z (activeReference Z Y))) :
    ∀ {x y : V},
      (x, y) ∈
          (fun e : Vertex V × Vertex V ↦
            (project e.1, project e.2)) ''
            {e | e ∈ F ∧ project e.1 ≠ project e.2} →
        x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y := by
  rintro x y ⟨e, ⟨heF, heProper⟩, hexy⟩
  have heFamily := hF heF
  simp only [familyEdges, Set.mem_iUnion] at heFamily
  rcases heFamily with ⟨P, ⟨p, hp, hpne, rfl⟩, heP⟩
  have heRoles := lift_edge_roles_of_project_ne Z p hpne heP heProper
  change (project e.1, project e.2) = (x, y) at hexy
  have hex : project e.1 = x := congrArg Prod.fst hexy
  have hey : project e.2 = y := congrArg Prod.snd hexy
  have hpActive : (.inl p : Gamma.DPath) ∈ activePaths Z := by
    refine ⟨hp, p.start, p.start_mem_support,
      p.finish, p.finish_mem_support, hpne⟩
  constructor
  · intro hxIsolated
    have hxIsolated' : project e.1 ∈ isolatedVertices Y :=
      hex ▸ hxIsolated
    have hxSupport : project e.1 ∈ p.support :=
      (p.edgeSet_subset_support_prod heRoles.2.2).1
    have hxActiveReference :
        Gamma.trivialPath (project e.1) ∈ activeReference Z Y :=
      trivialPath_mem_activeReference_of_active_support Z hpActive
        hxSupport hxIsolated'
    have hxTerminal :=
      outgoing_mem_terminalFrontier_canonicalPeeledReferenceLift_of_trivial
        Z hxActiveReference
    apply (hpure heF).2
    rw [heRoles.1]
    exact hxTerminal
  · intro hyIsolated
    have hyIsolated' : project e.2 ∈ isolatedVertices Y :=
      hey ▸ hyIsolated
    have hyInitialY : project e.2 ∈ Gamma.initialSet Y :=
      ⟨Gamma.trivialPath (project e.2), hyIsolated', rfl⟩
    have hySupport : project e.2 ∈ p.support :=
      (p.edgeSet_subset_support_prod heRoles.2.2).2
    have hyActiveReference :
        Gamma.trivialPath (project e.2) ∈ activeReference Z Y :=
      trivialPath_mem_activeReference_of_active_support Z hpActive
        hySupport hyIsolated'
    have hyVertexActiveReference :
        project e.2 ∈ Gamma.vertexSet (activeReference Z Y) :=
      ⟨Gamma.trivialPath (project e.2), hyActiveReference, by simp⟩
    have hyJunction : IsJunction Z (project e.2) :=
      junction_of_initial_of_mem_finiteEdge Z p hp heRoles.2.2
        (hsource hyInitialY)
    exact hnoJunction hyVertexActiveReference hyJunction

/-- The directly consumable finite-word form of
`properForwardImage_endpoints_not_isolated`. -/
theorem intervalSafe_properForwardImage_endpoints_not_isolated
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y))
    (Q : FiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z)
      (liftedReferencePaths Z (activeReference Z Y)))
    (hQ : Q.IsIntervalSafe) :
    ∀ {x y : V},
      (x, y) ∈
          (fun e : Vertex V × Vertex V ↦
            (project e.1, project e.2)) ''
            {e | e ∈ Q.forwardEdges ∧
              project e.1 ≠ project e.2} →
        x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y := by
  exact properForwardImage_endpoints_not_isolated Z hsource hnoJunction
    Q.forwardEdges_subset_familyEdges hQ.endpoint_pure

/-- The fixed forward warp used by the canonical coloured occurrence
construction. -/
abbrev canonicalActiveLift (Z : FracturedWarp Gamma) :
    Set (web Gamma Z).DPath :=
  liftedActiveFinitePaths Z

/-- The peeled canonical reference warp. -/
abbrev canonicalPeeledReferenceLift (Z : FracturedWarp Gamma)
    (Y : Set Gamma.DPath) : Set (web Gamma Z).DPath :=
  liftedReferencePaths Z (activeReference Z Y)

/-- Every lifted-reference vertex projects to the peeled downstairs
reference carrier.  The converse for an arbitrary role-copy is deliberately
false; endpoint-role coverage is proved separately below. -/
theorem project_mem_vertexSet_activeReference_of_mem_canonicalLift
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) {z : Vertex V} :
    z ∈ (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y) →
      project z ∈ Gamma.vertexSet (activeReference Z Y) := by
  rintro ⟨P, ⟨p, hp, rfl⟩, hzp⟩
  refine ⟨.inl p, hp, ?_⟩
  change z ∈ (referenceLiftFinitePath Z p).support at hzp
  change project z ∈ p.support
  rw [← project_image_referenceLiftFinitePath_support Z p]
  exact ⟨z, hzp, rfl⟩

/-- Every active downstairs initial has its outgoing copy in the canonical
forward warp. -/
theorem outgoing_mem_initialSet_canonicalActiveLift
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) {x : V}
    (hx : x ∈ Gamma.initialSet (activePaths Z)) :
    outgoing x ∈ (web Gamma Z).initialSet (canonicalActiveLift Z) := by
  rcases hx with ⟨P, ⟨hPZ, hPnt⟩, hPx⟩
  rcases hZfinite hPZ with ⟨p, rfl⟩
  have hpne : p.start ≠ p.finish :=
    finite_start_ne_finish_of_nontrivial p hPnt
  change p.start = x at hPx
  subst x
  exact ⟨.inl (lift Z p hpne),
    lift_mem_liftedActiveFinitePaths Z hPZ hpne, rfl⟩

/-- Every active downstairs finite terminal has its incoming copy in the
canonical forward warp. -/
theorem incoming_mem_terminalFrontier_canonicalActiveLift
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) {x : V}
    (hx : x ∈ Gamma.terminalFrontier (activePaths Z)) :
    incoming x ∈
      (web Gamma Z).terminalFrontier (canonicalActiveLift Z) := by
  rcases hx with ⟨P, ⟨hPZ, hPnt⟩, hPx⟩
  rcases hZfinite hPZ with ⟨p, rfl⟩
  have hpne : p.start ≠ p.finish :=
    finite_start_ne_finish_of_nontrivial p hPnt
  change some p.finish = some x at hPx
  have hfinish : p.finish = x := Option.some.inj hPx
  subst x
  exact ⟨.inl (lift Z p hpne),
    lift_mem_liftedActiveFinitePaths Z hPZ hpne, rfl⟩

/-- Every peeled-reference initial has its uniform outgoing copy in the
canonical reference lift, including singleton owners. -/
theorem outgoing_mem_initialSet_canonicalPeeledReferenceLift
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y) {x : V}
    (hx : x ∈ Gamma.initialSet (activeReference Z Y)) :
    outgoing x ∈ (web Gamma Z).initialSet
      (canonicalPeeledReferenceLift Z Y) := by
  rcases hx with ⟨P, hP, hPx⟩
  rcases hYfinite ((activeReference_subset Z Y) hP) with ⟨p, rfl⟩
  change p.start = x at hPx
  subst x
  exact ⟨.inl (referenceLiftFinitePath Z p),
    referenceLiftFinitePath_mem_liftedReferencePaths Z hP,
    referenceLiftFinitePath_start Z p⟩

/-- At a common active terminal, the no-junction hypothesis eliminates the
singleton reference case; hence the reference lift really ends at the
incoming copy. -/
theorem incoming_mem_terminalFrontier_canonicalPeeledReferenceLift
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y)) {x : V}
    (hxZ : x ∈ Gamma.terminalFrontier (activePaths Z))
    (hxY : x ∈ Gamma.terminalFrontier (activeReference Z Y)) :
    incoming x ∈ (web Gamma Z).terminalFrontier
      (canonicalPeeledReferenceLift Z Y) := by
  rcases hxY with ⟨P, hP, hPterm⟩
  have hPY : P ∈ Y := activeReference_subset Z Y hP
  rcases hYfinite hPY with ⟨p, rfl⟩
  change some p.finish = some x at hPterm
  have hpfinish : p.finish = x := Option.some.inj hPterm
  have hpne : p.start ≠ p.finish := by
    intro heq
    have hxInitialY : x ∈ Gamma.initialSet Y := by
      refine ⟨.inl p, hPY, ?_⟩
      exact heq.trans hpfinish
    have hxInitialZ := hsource hxInitialY
    have hxTerminalZ : x ∈ Gamma.terminalFrontier Z.paths := by
      rcases hxZ with ⟨Q, hQ, hQterm⟩
      exact ⟨Q, hQ.1, hQterm⟩
    have hxVertexActiveReference :
        x ∈ Gamma.vertexSet (activeReference Z Y) :=
      ⟨.inl p, hP, hpfinish ▸ p.finish_mem_support⟩
    exact (hnoJunction hxVertexActiveReference)
      ⟨hxInitialZ, hxTerminalZ⟩
  subst x
  refine ⟨.inl (referenceLiftFinitePath Z p),
    referenceLiftFinitePath_mem_liftedReferencePaths Z hP, ?_⟩
  rw [referenceLiftFinitePath, dif_neg hpne]
  rfl

/-- Exact downstairs source and role of a canonical active lifted initial. -/
theorem initial_data_canonicalActiveLift (Z : FracturedWarp Gamma)
    {z : Vertex V}
    (hz : z ∈ (web Gamma Z).initialSet (canonicalActiveLift Z)) :
    ∃ x ∈ Gamma.initialSet (activePaths Z), z = outgoing x := by
  rcases hz with ⟨P, ⟨p, hp, hpne, rfl⟩, hz⟩
  have hz' : outgoing p.start = z := hz
  refine ⟨p.start, ?_, hz'.symm⟩
  refine ⟨.inl p, ⟨hp, ?_⟩, rfl⟩
  exact ⟨p.start, p.start_mem_support, p.finish,
    p.finish_mem_support, hpne⟩

/-- Exact downstairs finite terminal and role of a canonical active lifted
terminal. -/
theorem terminal_data_canonicalActiveLift (Z : FracturedWarp Gamma)
    {z : Vertex V}
    (hz : z ∈ (web Gamma Z).terminalFrontier (canonicalActiveLift Z)) :
    ∃ x ∈ Gamma.terminalFrontier (activePaths Z), z = incoming x := by
  rcases hz with ⟨P, ⟨p, hp, hpne, rfl⟩, hz⟩
  change some (incoming p.finish) = some z at hz
  have hz' : incoming p.finish = z := Option.some.inj hz
  refine ⟨p.finish, ?_, hz'.symm⟩
  refine ⟨.inl p, ⟨hp, ?_⟩, rfl⟩
  exact ⟨p.start, p.start_mem_support, p.finish,
    p.finish_mem_support, hpne⟩

/-- Exact downstairs source and role of a peeled canonical reference
initial. -/
theorem initial_data_canonicalPeeledReferenceLift
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath} {z : Vertex V}
    (hz : z ∈ (web Gamma Z).initialSet
      (canonicalPeeledReferenceLift Z Y)) :
    ∃ x ∈ Gamma.initialSet (activeReference Z Y), z = outgoing x := by
  rcases hz with ⟨P, ⟨p, hp, rfl⟩, hz⟩
  have hz' : outgoing p.start = z := by
    exact (referenceLiftFinitePath_start Z p).symm.trans hz
  exact ⟨p.start, ⟨.inl p, hp, rfl⟩, hz'.symm⟩

/-- Canonical lifting preserves the source inclusion needed by the coloured
dichotomy after covered singleton components are peeled. -/
theorem initialSet_canonicalPeeledReferenceLift_subset_activeLift
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    (web Gamma Z).initialSet (canonicalPeeledReferenceLift Z Y) ⊆
      (web Gamma Z).initialSet (canonicalActiveLift Z) := by
  intro z hz
  rcases initial_data_canonicalPeeledReferenceLift Z hz with
    ⟨x, hx, rfl⟩
  apply outgoing_mem_initialSet_canonicalActiveLift Z hZfinite
  exact activeReference_initials_subset_activePaths Z hboundary hY
    hZfinite hsource hx

/-- An exposed canonical active source projects outside the entire original
reference carrier.  Peeling covered singleton owners does not weaken the
downstairs conclusion. -/
theorem project_not_mem_vertexSet_of_initial_sdiff
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hYfinite : Gamma.HasFiniteCharacter Y) {z : Vertex V}
    (hzForward : z ∈
      (web Gamma Z).initialSet (canonicalActiveLift Z))
    (hzReference : z ∉
      (web Gamma Z).initialSet (canonicalPeeledReferenceLift Z Y)) :
    project z ∉ Gamma.vertexSet Y := by
  rcases initial_data_canonicalActiveLift Z hzForward with
    ⟨x, hxActive, rfl⟩
  have hxNotActiveReference :
      x ∉ Gamma.initialSet (activeReference Z Y) := by
    intro hx
    exact hzReference
      (outgoing_mem_initialSet_canonicalPeeledReferenceLift Z
        hYfinite hx)
  have hxDiff :
      x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet (activeReference Z Y) :=
    ⟨hxActive, hxNotActiveReference⟩
  rw [active_initial_difference_eq (Y := Y) Z] at hxDiff
  apply hboundary.initial_outside
  refine ⟨?_, hxDiff.2⟩
  rcases hxActive with ⟨p, hp, hpx⟩
  exact ⟨p, hp.1, hpx⟩

/-- An exposed finite terminal of the canonical active lift projects outside
the entire original reference carrier.  The no-junction hypothesis is what
rules out the outgoing-role terminal of a peeled singleton reference owner. -/
theorem project_not_mem_vertexSet_of_terminal_sdiff
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y)) {z : Vertex V}
    (hzForward : z ∈
      (web Gamma Z).terminalFrontier (canonicalActiveLift Z))
    (hzReference : z ∉
      (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y)) :
    project z ∉ Gamma.vertexSet Y := by
  rcases terminal_data_canonicalActiveLift Z hzForward with
    ⟨x, hxActive, rfl⟩
  have hactive : BoundaryAligned (activePaths Z) (activeReference Z Y) :=
    boundaryAligned_active Z hboundary hY
  have hxNotActiveReference :
      x ∉ Gamma.vertexSet (activeReference Z Y) := by
    intro hxReference
    have hxTerminalReference :
        x ∈ Gamma.terminalFrontier (activeReference Z Y) :=
      hactive.2 ⟨hxActive, hxReference⟩
    have hxLifted :=
      incoming_mem_terminalFrontier_canonicalPeeledReferenceLift
        Z hYfinite hsource hnoJunction hxActive hxTerminalReference
    exact hzReference
      (terminalFrontier_subset_vertexSet
        (canonicalPeeledReferenceLift Z Y) hxLifted)
  have hxDiff :
      x ∈ Gamma.terminalFrontier (activePaths Z) \
        Gamma.vertexSet (activeReference Z Y) :=
    ⟨hxActive, hxNotActiveReference⟩
  rw [active_terminal_difference_eq (Y := Y) Z] at hxDiff
  exact hxDiff.2

/-- The fixed-role canonical pair retains the literal boundary alignment
needed by the endpoint-pure coloured dichotomy. -/
theorem boundaryAligned_canonicalLift
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y)) :
    BoundaryAligned (canonicalActiveLift Z)
      (canonicalPeeledReferenceLift Z Y) := by
  have hactive : BoundaryAligned (activePaths Z) (activeReference Z Y) :=
    boundaryAligned_active Z hboundary hY
  constructor
  · rintro z ⟨hzInitial, hzReference⟩
    rcases initial_data_canonicalActiveLift Z hzInitial with ⟨x, hx, rfl⟩
    have hxReference : x ∈ Gamma.vertexSet (activeReference Z Y) :=
      project_mem_vertexSet_activeReference_of_mem_canonicalLift
        Z Y hzReference
    have hxInitial := hactive.1 ⟨hx, hxReference⟩
    exact outgoing_mem_initialSet_canonicalPeeledReferenceLift
      Z hYfinite hxInitial
  · rintro z ⟨hzTerminal, hzReference⟩
    rcases terminal_data_canonicalActiveLift Z hzTerminal with ⟨x, hx, rfl⟩
    have hxReference : x ∈ Gamma.vertexSet (activeReference Z Y) :=
      project_mem_vertexSet_activeReference_of_mem_canonicalLift
        Z Y hzReference
    have hxTerminal := hactive.2 ⟨hx, hxReference⟩
    exact incoming_mem_terminalFrontier_canonicalPeeledReferenceLift
      Z hYfinite hsource hnoJunction hx hxTerminal

/-- All fixed pair hypotheses used before selecting a source in the coloured
dichotomy. -/
structure CanonicalDichotomyGeometry (Z : FracturedWarp Gamma)
    (Y : Set Gamma.DPath) : Prop where
  forward_isWarp : (web Gamma Z).IsWarp (canonicalActiveLift Z)
  reference_isWarp :
    (web Gamma Z).IsWarp (canonicalPeeledReferenceLift Z Y)
  forward_finite :
    (web Gamma Z).HasFiniteCharacter (canonicalActiveLift Z)
  reference_finite :
    (web Gamma Z).HasFiniteCharacter (canonicalPeeledReferenceLift Z Y)
  source_subset :
    (web Gamma Z).initialSet (canonicalPeeledReferenceLift Z Y) ⊆
      (web Gamma Z).initialSet (canonicalActiveLift Z)
  boundary_aligned : BoundaryAligned (canonicalActiveLift Z)
    (canonicalPeeledReferenceLift Z Y)

/-- Construction of the complete fixed-pair geometry from the genuine
downstairs boundary data. -/
theorem canonicalDichotomyGeometry
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction :
      NoJunctionOnReference Z (activeReference Z Y)) :
    CanonicalDichotomyGeometry Z Y := {
  forward_isWarp := liftedActiveFinitePaths_isWarp Z
  reference_isWarp := liftedReferencePaths_isWarp Z
    (activeReference_isWarp Z hY)
  forward_finite := liftedActiveFinitePaths_hasFiniteCharacter Z
  reference_finite := liftedReferencePaths_hasFiniteCharacter Z
    (activeReference Z Y)
  source_subset :=
    initialSet_canonicalPeeledReferenceLift_subset_activeLift Z
      hboundary hY hZfinite hYfinite hsource
  boundary_aligned := boundaryAligned_canonicalLift Z hboundary hY
    hZfinite hYfinite hsource hnoJunction }

#print axioms canonicalDichotomyGeometry
#print axioms project_not_mem_vertexSet_of_initial_sdiff
#print axioms project_not_mem_vertexSet_of_terminal_sdiff
#print axioms intervalSafe_properForwardImage_endpoints_not_isolated

end Erdos599.Blueprint.LinkageBlueprint.FracturedCanonicalBoundary
