/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayContinuationRepair
import ErdosProblems.Erdos599.HalfwayCurrentTargetRow
import ErdosProblems.Erdos599.HalfwayStageGeometry
import ErdosProblems.Erdos599.FracturedWarpOfWarp

/-!
# Concrete pieces of the club-stage seed

This file records the parts of `ClubStageSeedSystem` which follow directly
from the already public Section 9 data.

* An honest warp is canonically a fractured warp.
* A full source--target linkage therefore supplies all four endpoint and
  finite-character conditions required of the fractured family.
* The vertex set of the current blueprint is a canonical closure seed of
  cardinality at most `kappa` contained in the later roof.

The last lemma isolates the remaining geometric obligation.  The
`AssignmentClosureContext` demanded by the global transaction implies that
every assigned alternating path leaves the closed set.  This conclusion is
not a consequence of endpoint purity of a full linkage: it is exactly what
the cut-dependent outside-fragment construction of Assertion 9.31 must prove.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V}

namespace Alternating.FracturedWarp

/-- Complete a partial source row by stopping every source outside `A`
immediately.  This is the concrete family constructed by
`exists_provisionalTargetRow_of_current`. -/
def sourceCompletedRow (A : Set V) (P : Set Gamma.DPath) :
    Set Gamma.DPath :=
  P ∪ Gamma.trivialPath '' (Gamma.source \ A)

theorem trivialPath_mem_sourceCompletedRow
    (A : Set V) (P : Set Gamma.DPath) {x : V}
    (hx : x ∈ Gamma.source \ A) :
    Gamma.trivialPath x ∈ sourceCompletedRow A P := by
  exact Or.inr ⟨x, hx, rfl⟩

/-- Every source added as a trivial remainder is a terminal of the
provisional row. -/
theorem sourceDiff_subset_terminalFrontier_sourceCompletedRow
    (A : Set V) (P : Set Gamma.DPath) :
    Gamma.source \ A ⊆
      Gamma.terminalFrontier (sourceCompletedRow A P) := by
  intro x hx
  exact ⟨Gamma.trivialPath x, trivialPath_mem_sourceCompletedRow A P hx,
    Gamma.terminal?_trivialPath x⟩

/-- Regard a linkage as a fractured warp without changing any path. -/
def ofLinkageBetween {A B : Set V} {L : Set Gamma.DPath}
    (hL : CardinalInduction.IsLinkageBetween Gamma A B L) :
    FracturedWarp Gamma :=
  ofWarp L hL.isWarp

@[simp] theorem paths_ofLinkageBetween {A B : Set V}
    {L : Set Gamma.DPath}
    (hL : CardinalInduction.IsLinkageBetween Gamma A B L) :
    (ofLinkageBetween hL).paths = L :=
  rfl

theorem initialSet_ofLinkageBetween {A B : Set V}
    {L : Set Gamma.DPath}
    (hL : CardinalInduction.IsLinkageBetween Gamma A B L) :
    Gamma.initialSet (ofLinkageBetween hL).paths = A := by
  simpa using hL.initialSet_eq

theorem terminalFrontier_ofLinkageBetween_subset {A B : Set V}
    {L : Set Gamma.DPath}
    (hL : CardinalInduction.IsLinkageBetween Gamma A B L) :
    Gamma.terminalFrontier (ofLinkageBetween hL).paths ⊆ B := by
  simpa using hL.terminalFrontier_subset

theorem finiteCharacter_ofLinkageBetween {A B : Set V}
    {L : Set Gamma.DPath}
    (hL : CardinalInduction.IsLinkageBetween Gamma A B L) :
    Gamma.HasFiniteCharacter (ofLinkageBetween hL).paths := by
  change Gamma.HasFiniteCharacter L
  exact hL.finiteCharacter

/-- A full linkage gives precisely the source, target, and finite-character
fields of the fractured-family part of `ClubStageSeedSystem`. -/
theorem fullLinkage_fractured_fields {L : Set Gamma.DPath}
    (hL : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source Gamma.target L) :
    Gamma.initialSet (ofLinkageBetween hL).paths ⊆ Gamma.source ∧
      Gamma.terminalFrontier (ofLinkageBetween hL).paths ⊆ Gamma.target ∧
      Gamma.HasFiniteCharacter (ofLinkageBetween hL).paths := by
  exact ⟨by simpa using hL.initialSet_eq.le,
    terminalFrontier_ofLinkageBetween_subset hL,
    finiteCharacter_ofLinkageBetween hL⟩

/-- If the reference initials lie in the web source, a full linkage also
supplies the initial-frontier comparison needed by simultaneous assignment. -/
theorem referenceInitials_subset_fullLinkage
    {Y L : Set Gamma.DPath}
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hL : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source Gamma.target L) :
    Gamma.initialSet Y ⊆
      Gamma.initialSet (ofLinkageBetween hL).paths := by
  change Gamma.initialSet Y ⊆ Gamma.initialSet L
  rw [hL.initialSet_eq]
  exact hYsource

/-- A single internal finite endpoint outside the web target refutes any
attempt to treat all fracture endpoints as ambient target vertices.  This is
why the stage interface uses the actual fractured boundary and an arbitrary
local closing-up side instead of such a global endpoint assumption. -/
theorem not_terminalFrontier_subset_target_of_internal_terminal
    (Zf : FracturedWarp Gamma) {p : Gamma.DPath} {v : V}
    (hp : p ∈ Zf.paths) (hterminal : Gamma.terminal? p = some v)
    (hv : v ∉ Gamma.target) :
    ¬ Gamma.terminalFrontier Zf.paths ⊆ Gamma.target := by
  intro htarget
  exact hv (htarget ⟨p, hp, hterminal⟩)

/-- Specialization of the preceding obstruction to an honest warp viewed as
a fractured warp. -/
theorem ofWarp_not_targetSide_of_internal_terminal
    {Z : Set Gamma.DPath} (hZ : Gamma.IsWarp Z)
    {p : Gamma.DPath} {v : V}
    (hp : p ∈ Z) (hterminal : Gamma.terminal? p = some v)
    (hv : v ∉ Gamma.target) :
    ¬ Gamma.terminalFrontier (ofWarp Z hZ).paths ⊆ Gamma.target :=
  not_terminalFrontier_subset_target_of_internal_terminal
    (ofWarp Z hZ) hp hterminal hv

/-- Hence the provisional current-cardinal row cannot be the seed's
fractured family whenever there is an undesignated source outside the
target.  This is the exact terminal mismatch, independent of any later
closure construction. -/
theorem sourceCompletedRow_not_targetSide
    (A : Set V) (P : Set Gamma.DPath)
    (hrow : Gamma.IsWarp (sourceCompletedRow A P))
    {x : V} (hx : x ∈ Gamma.source \ A) (hxTarget : x ∉ Gamma.target) :
    ¬ Gamma.terminalFrontier
      (ofWarp (sourceCompletedRow A P) hrow).paths ⊆ Gamma.target := by
  apply not_terminalFrontier_subset_target_of_internal_terminal
    (ofWarp (sourceCompletedRow A P) hrow)
    (p := Gamma.trivialPath x) (v := x)
  · exact trivialPath_mem_sourceCompletedRow A P hx
  · exact Gamma.terminal?_trivialPath x
  · exact hxTarget

theorem sourceCompletedRow_not_targetSide_of_disjoint
    (A : Set V) (P : Set Gamma.DPath)
    (hrow : Gamma.IsWarp (sourceCompletedRow A P))
    (hdisjoint : Disjoint Gamma.source Gamma.target)
    (hmissing : (Gamma.source \ A).Nonempty) :
    ¬ Gamma.terminalFrontier
      (ofWarp (sourceCompletedRow A P) hrow).paths ⊆ Gamma.target := by
  obtain ⟨x, hx⟩ := hmissing
  exact sourceCompletedRow_not_targetSide A P hrow hx
    (Set.disjoint_left.1 hdisjoint hx.1)

end Alternating.FracturedWarp

namespace Blueprint

/-- The roof-containment lemma needed by the hammock closure only requires
safe paths at eligible endpoint pairs.  This endpoint-restricted statement
does not quantify over arbitrary trivial alternating paths and is therefore
the appropriate replacement for the globally overstrong `hSafeRoof`
hypothesis of the current closing-up interface. -/
theorem allHammockVertices_subset_roof_of_eligible
    {Y : Set Gamma.DPath} {rho : Cardinal.{u}}
    {ZBefore innerRoof roof : Set V}
    (hSafeRoof : ∀ (u : V) (e : AltEnd V),
      HammockEligible ZBefore innerRoof roof u e →
      ∀ Q : AltPath Gamma.graph, IsSafe Y Q →
        Q.initial = u → HasEnd Q e → Q.vertexSet ⊆ roof) :
    allHammockVertices Gamma Y rho ZBefore innerRoof roof ⊆ roof := by
  intro x hx
  obtain ⟨q, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.1 hx
  have hQ := (chosenHammock_spec Gamma Y rho q).isHammock.1 Q.1 Q.2
  exact hSafeRoof q.1.1 q.1.2 q.2 Q.1 hQ.1 hQ.2.1 hQ.2.2 hxQ

end Blueprint

namespace Blueprint.LinkageBlueprint

variable {Y : Set Gamma.DPath} {kappa theta : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- Requiring *every* safe alternating path to lie in one set forces that
set to be the whole vertex space: trivial alternating paths are safe at
every vertex. -/
theorem roof_eq_univ_of_all_safe_vertexSet_subset
    (hY : Gamma.IsWarp Y) {roof : Set V}
    (hSafe : ∀ Q : AltPath Gamma.graph,
      IsSafe Y Q → Q.vertexSet ⊆ roof) :
    roof = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  have hv := hSafe (.trivial v) (Alternating.isSafe_trivial hY v)
  exact hv (by simp only [AltPath.vertexSet_trivial, Set.mem_singleton_iff])

/-- The honest recombination stored inside a fractured warp is still
available for edge-set arguments.  Simultaneous assignment itself is made on
the literal fractured family, so shared cut vertices remain endpoints. -/
theorem ClubStageSeedSystem.edgeWarp_isWarp
    (S : ClubStageSeedSystem C)
    (W : LinkageBlueprint Gamma Y kappa) (u : V) (X : Set V) :
    Gamma.IsWarp (S.fractured W u X).edgeWarp :=
  (S.fractured W u X).edgeWarp_isWarp

/-- The current blueprint vertices are the canonical first seed for the
omega closing-up operation.  They already include any scheduled real
terminal because the real part is spanning. -/
def canonicalClubInitialSeed
    (W : LinkageBlueprint Gamma Y kappa) (_u : V) : Set V :=
  W.vertexSet

theorem canonicalClubInitialSeed_card
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #(canonicalClubInitialSeed W u) ≤ kappa := by
  exact W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths

theorem canonicalClubInitialSeed_in_roof
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    canonicalClubInitialSeed W u ⊆ C.outerRoof := by
  exact hW.vertices_roofed

theorem scheduledTerminal_mem_canonicalClubInitialSeed
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hu : u ∈ W.realPart.terminals) :
    u ∈ canonicalClubInitialSeed W u :=
  hu.1

/-- The closure facts force each assigned path to have a vertex outside the
closed set.  Thus the full-linkage candidate above can be used only after a
genuine cut-dependent outside-fragment construction establishes this fact. -/
theorem assigned_not_subset_of_assignmentClosureContext
    {Zf : FracturedWarp Gamma}
    (A : SimultaneousAssignment Zf.paths Y)
    {X before innerRoof outerRoof : Set V}
    (hA : AssignmentClosureContext A X before innerRoof outerRoof)
    (s : {x // x ∈ Gamma.initialSet Zf.paths \ Gamma.initialSet Y}) :
    ¬ (A.assigned s).vertexSet ⊆ X :=
  hA.outside s

theorem no_assignmentClosureContext_of_assigned_subset
    {Zf : FracturedWarp Gamma}
    (A : SimultaneousAssignment Zf.paths Y)
    {X before innerRoof outerRoof : Set V}
    (s : {x // x ∈ Gamma.initialSet Zf.paths \ Gamma.initialSet Y})
    (hs : (A.assigned s).vertexSet ⊆ X) :
    ¬ AssignmentClosureContext A X before innerRoof outerRoof := by
  intro hA
  exact hA.outside s hs

end Blueprint.LinkageBlueprint

namespace CardinalInduction

/-- Public version of the elementary fact used by the provisional-row
constructor: a linkage to the ambient target supplies the required suffix
certificate for each of its initials. -/
theorem linksToTarget_of_linkageToAmbientTarget
    {A : Set V} {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma A Gamma.target P) :
    LinksToTarget Gamma P A := by
  intro a ha
  have haInitial : a ∈ Gamma.initialSet P := hP.initialSet_eq.symm ▸ ha
  obtain ⟨p, hpP, hpInitial⟩ := haInitial
  obtain ⟨q, rfl⟩ := hP.finiteCharacter hpP
  change q.start = a at hpInitial
  obtain ⟨r, hr, _hends, hsource⟩ :=
    hP.endpointPure (.inl q) hpP
  have hrq : r = q := by simpa using hr.symm
  subst r
  refine ⟨.inl q, hpP, q, rfl, ?_, ?_⟩
  · simpa only [hpInitial] using hsource
  · refine ⟨[], q.walk.support.tail, ?_, q.finish, ?_, ?_⟩
    · have hsupport :
          q.walk.support = q.start :: q.walk.support.tail := by
        have h := (List.cons_head_tail q.walk.support_ne_nil).symm
        simpa only [q.walk.head_support] using h
      exact hsupport.trans
        (congrArg (fun x ↦ x :: q.walk.support.tail) hpInitial)
    · apply hP.terminalFrontier_subset
      exact ⟨.inl q, hpP, rfl⟩
    · have hsupport :
          q.walk.support = q.start :: q.walk.support.tail := by
        have h := (List.cons_head_tail q.walk.support_ne_nil).symm
        simpa only [q.walk.head_support] using h
      have hfinish : q.finish ∈ q.start :: q.walk.support.tail := by
        rw [← hsupport]
        exact q.finish_mem_support
      simpa only [hpInitial] using hfinish

/-- Exact audit of the current-cardinal provisional row.  If even one
undesignated source is not already a target, the row produced from the
current extension clause has all four public row properties but its finite
frontier is not contained in the ambient target.  Consequently this row may
only be used through the local fractured-boundary interface. -/
theorem exists_provisionalTargetRow_not_targetSide_of_current
    {kappa : Cardinal.{u}}
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsUnhindered) (hNorm : Gamma.IsNormalized)
    {A : Set V} (hA : A ⊆ Gamma.source) (hcard : #A = kappa)
    (hmissing : ∃ x ∈ Gamma.source \ A, x ∉ Gamma.target) :
    ∃ Zf : FracturedWarp Gamma,
      Gamma.IsWarp Zf.paths ∧
      Gamma.HasFiniteCharacter Zf.paths ∧
      Gamma.initialSet Zf.paths = Gamma.source ∧
      LinksToTarget Gamma Zf.paths A ∧
      ¬ Gamma.terminalFrontier Zf.paths ⊆ Gamma.target := by
  obtain ⟨P, hP⟩ :=
    exists_designatedSourceLinkage_of_current hext Gamma hGamma hNorm hA hcard
  let W : Set Gamma.DPath :=
    Alternating.FracturedWarp.sourceCompletedRow A P
  have hcross : ∀ p ∈ P,
      ∀ q ∈ Gamma.trivialPath '' (Gamma.source \ A), p ≠ q →
        Disjoint p.support q.support := by
    intro p hp q hq _hpq
    obtain ⟨x, hx, rfl⟩ := hq
    rw [Gamma.support_trivialPath]
    apply Set.disjoint_singleton_right.2
    intro hxp
    have hxInitial : x = p.initial :=
      hNorm.eq_initial_of_mem_path p hxp hx.1
    have hpInitial : p.initial ∈ A := by
      rw [← hP.initialSet_eq]
      exact ⟨p, hp, rfl⟩
    exact hx.2 (hxInitial.symm ▸ hpInitial)
  have hwarp : Gamma.IsWarp W := by
    apply Set.PairwiseDisjoint.union hP.isWarp
      (Gamma.isWarp_trivialPaths (Gamma.source \ A))
    exact hcross
  have hfinite : Gamma.HasFiniteCharacter W := by
    intro p hp
    rcases hp with hp | hp
    · exact hP.finiteCharacter hp
    · obtain ⟨x, _hx, rfl⟩ := hp
      exact ⟨FinitePath.trivial Gamma.graph x, rfl⟩
  have hinitial : Gamma.initialSet W = Gamma.source := by
    change Gamma.initialSet
      (P ∪ (Gamma.trivialPath '' (Gamma.source \ A))) = Gamma.source
    rw [Gamma.initialSet_union, Gamma.initialSet_trivialPaths,
      hP.initialSet_eq, Set.union_comm, Set.sdiff_union_of_subset hA]
  have hlinks : LinksToTarget Gamma W A := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ :=
      linksToTarget_of_linkageToAmbientTarget hP a ha
    exact ⟨p, Or.inl hp, hpa⟩
  obtain ⟨x, hx, hxTarget⟩ := hmissing
  let Zf : FracturedWarp Gamma :=
    Alternating.FracturedWarp.ofWarp W hwarp
  refine ⟨Zf, ?_, ?_, ?_, ?_, ?_⟩
  · change Gamma.IsWarp W
    exact hwarp
  · change Gamma.HasFiniteCharacter W
    exact hfinite
  · change Gamma.initialSet W = Gamma.source
    exact hinitial
  · change LinksToTarget Gamma W A
    exact hlinks
  · exact Alternating.FracturedWarp.sourceCompletedRow_not_targetSide
      A P hwarp hx hxTarget

end CardinalInduction

end Erdos599
