/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFracturedAssignmentCompiler
import ErdosProblems.Erdos599.HalfwaySelectedCut
import ErdosProblems.Erdos599.WholeFamilyOrientedReplacementExact

/-!
# Closing after the later linkage has been selected

The literal order written in Assertion 9.31 closes `X` before invoking the
extension clause which selects the later linkage `W`.  With that order,
Theorem 4.12 does not ensure that an assigned safe alternating path avoids
`X` internally, so Claim 2 cannot be applied to the whole path.

There is a source-faithful repair which keeps the same cardinal bounds.  The
later finite-character linkage is independent of the closing set: select it
first, and include it as the extra path family in the omega closure.  Closure
under `W` still costs at most `kappa`, because a warp has at most one member
through each previously selected vertex and every member is finite.  At the
resulting set, both the forward owner family `W` and the backward reference
family `Y` are path-closed.  Hence every bracket-safe assignment beginning at
an outside hole is wholly disjoint from `X`.  The ordinary fractured
assignment compiler therefore supplies the exact Claim-2 witnesses, without
an endpoint-clean selection hypothesis or a contact-splitting assumption.

This file packages that corrected dependency order.  All nontrivial path
geometry is proved in `HalfwaySelectedCut`; the theorem below combines it
with the existing omega closure and fractured-assignment compiler.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- All data needed once the later linkage has been selected before the
closing operation.  `later` is the linkage which will subsequently be cut at
the resulting set; it is not an arbitrary post-closure family. -/
structure LinkageFirstClosureSeed where
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  targetSlice : Set V
  targetSide : Set V
  initialSeed : Set V
  later : Set Gamma.DPath
  Preserves : FinitePath Gamma.graph → Prop
  target_paths : ∀ v ∈ targetSlice ∩ outerRoof,
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ targetSide ∧
        p.support ⊆ outerRoof ∧ Preserves p
  reference_isWarp : Gamma.IsWarp Y
  reference_finite : Gamma.HasFiniteCharacter Y
  reference_in_roof : ∀ p ∈ Y, p.support ⊆ outerRoof
  later_isWarp : Gamma.IsWarp later
  later_finite : Gamma.HasFiniteCharacter later
  later_in_roof : ∀ p ∈ later, p.support ⊆ outerRoof
  safe_in_roof : EligibleHammocksContainedInRoof Gamma Y
    before innerRoof outerRoof
  kappa_infinite : aleph0 ≤ kappa
  before_card : #before ≤ kappa
  initial_card : #initialSeed ≤ kappa
  initial_in_roof : initialSeed ⊆ outerRoof

/-- Linkage-first seed with the boundary geometry selected at the actual
closed set. -/
structure LinkageFirstClosedCutSeed extends
    LinkageFirstClosureSeed (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  cut_boundary : ∀ X : Set V,
    initialSeed ⊆ X →
    #X ≤ kappa →
    HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa →
    LargeHammockClosed Gamma Y X before innerRoof outerRoof kappa →
    HasPreservingTargetPaths Gamma targetSlice X targetSide Preserves →
    ClosedUnderPaths Gamma Y X →
    ClosedUnderPaths Gamma later X →
    ContainedInRoof X outerRoof →
    OutsideCutBoundary (Y := Y) later X before innerRoof outerRoof

namespace LinkageFirstClosedCutSeed

/-- Selecting the later linkage first repairs the Claim 1/Claim 2 handoff.
The returned request is the existing downstream request, so no changes to
the global blueprint transaction are required. -/
theorem exists_closedRequest
    {persistent : Set V}
    (S : LinkageFirstClosedCutSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) :
    Nonempty (ClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, htarget,
      hreference, hlater, hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_rowClosure Gamma Y S.later
      kappa kappa S.before S.innerRoof S.outerRoof S.targetSlice
      S.targetSide S.initialSeed S.Preserves S.target_paths
      S.reference_isWarp S.later_isWarp S.reference_in_roof
      S.later_in_roof S.safe_in_roof S.kappa_infinite (le_refl kappa)
      S.before_card S.initial_card S.initial_in_roof
  let boundary : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp S.later X,
      OutsideCutBoundary (Y := Y) S.later X
        S.before S.innerRoof S.outerRoof :=
    fun _ ↦ S.cut_boundary X hseed hcard hclosed hlarge htarget hreference
      hlater hroof
  let assigned : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp S.later X,
      FracturedAssignmentPeel.BracketFracturedAssignment F.outside.holes Y :=
    fun F ↦ (F.outside.exists_bracketFracturedAssignment
      ((boundary F).fractured_boundaryAligned F.outside)
      S.reference_isWarp S.reference_finite
      ((boundary F).fractured_referenceInitials F.outside)).some
  obtain ⟨D⟩ :=
    SelectedClosedFracturedCut.exists_of_literalOutsideCut_and_rowClosure
      S.later_isWarp S.later_finite hlater hreference boundary assigned
  exact ⟨D.toClosedFracturedReplacementRequest hclosed⟩

end LinkageFirstClosedCutSeed

/-- Scheduler-facing provider in the repaired dependency order.  A request
first selects its later linkage and all boundary data, then
`exists_closedRequest` performs the omega closure and Claim-2 compilation. -/
def LinkageFirstClosedCutSeedProvider
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        Nonempty (LinkageFirstClosedCutSeed
          (Gamma := Gamma) (Y := Y) (kappa := kappa))

/-- The repaired provider feeds the existing global transaction compiler. -/
theorem closedRequestProvider_of_linkageFirstSeedProvider
    {T Z persistent : Set V}
    (hseed : LinkageFirstClosedCutSeedProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u hW hpersistent hu
  exact (hseed W u hW hpersistent hu).some.exists_closedRequest

/-! ## Audit: the linkage-first boundary conflict -/

/-- If the later linkage is path-closed at `X`, every literal outside
fragment initial is outside `X`.  Thus the boundary condition requiring all
reference initials to occur as outside-fragment initials forces every
reference initial outside the closed set. -/
theorem referenceInitials_disjoint_of_laterClosed
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (hWclosed : ClosedUnderPaths Gamma W X)
    (B : OutsideCutBoundary (Y := Y) W X
      before innerRoof outerRoof) :
    Disjoint (Gamma.initialSet Y) X := by
  rw [Set.disjoint_left]
  intro x hxY hxX
  have hxOutside := B.reference_initials hxY
  rcases hxOutside with hxOutgoing | hxRoot
  · obtain ⟨_hxX, y, hxy⟩ := hxOutgoing
    have hxCarrier : x ∈ outsideCarrier W X :=
      (outsideFamilyEdges_endpoints W X hxy).1
    exact Set.disjoint_left.1
      (outsideCarrier_disjoint_of_closedUnderPaths W X hWclosed)
      hxCarrier hxX
  · exact hxRoot.2.1 hxX

/-- Closing under the reference family upgrades the preceding conflict from
reference initials to the whole reference carrier.  Hence a linkage-first
cut boundary can exist only when the closed set is disjoint from every
reference path.  The natural Section 9 seed contains old reference
vertices, so this rules out using the linkage-first adapter in the public
half-way construction. -/
theorem referenceVertexSet_disjoint_of_linkageFirstBoundary
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (hWclosed : ClosedUnderPaths Gamma W X)
    (hYclosed : ClosedUnderPaths Gamma Y X)
    (B : OutsideCutBoundary (Y := Y) W X
      before innerRoof outerRoof) :
    Disjoint (Gamma.vertexSet Y) X := by
  rw [Set.disjoint_left]
  intro x hxY hxX
  obtain ⟨p, hpY, hxp⟩ := hxY
  have hpX : p.support ⊆ X := hYclosed p hpY ⟨x, hxp, hxX⟩
  have hpInitial : p.initial ∈ Gamma.initialSet Y := ⟨p, hpY, rfl⟩
  exact Set.disjoint_left.1
    (referenceInitials_disjoint_of_laterClosed hWclosed B)
    hpInitial (hpX p.initial_mem_support)

/-! ## Ladder-specialized linkage-first seeds -/

/-- Concrete linkage-first data at one selected pair of club stages.

The later linkage is selected as a function of the current blueprint and
scheduled terminal *before* the omega closure is run.  All of its closure
and roof facts are therefore stated at the fixed ladder geometry `C`.  The
only cut-dependent field is `cut_boundary`; it is invoked after the unique
closed set has been constructed with closure under both the reference and
the selected later linkage.

This is the linkage-first counterpart of `ClosureFirstClubStageSeedSystem`.
In particular it does not contain a closed set, a fractured assignment, or
a result blueprint. -/
structure LinkageFirstClubStageSeedSystem
    (C : ClubStageGeometry Gamma Y kappa theta) where
  Preserves : FinitePath Gamma.graph → Prop
  target_paths : ∀ v ∈ C.oldSlice ∩ C.outerRoof,
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ C.newSlice ∧
        p.support ⊆ C.outerRoof ∧ Preserves p
  reference_isWarp : Gamma.IsWarp Y
  reference_finite : Gamma.HasFiniteCharacter Y
  reference_in_roof : ∀ p ∈ Y, p.support ⊆ C.outerRoof
  safe_in_roof : EligibleHammocksContainedInRoof Gamma Y
    C.before C.innerRoof C.outerRoof
  initialSeed : LinkageBlueprint Gamma Y kappa → V → Set V
  later : LinkageBlueprint Gamma Y kappa → V → Set Gamma.DPath
  initial_card : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        #(initialSeed W u) ≤ kappa
  initial_in_roof : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        initialSeed W u ⊆ C.outerRoof
  later_isWarp : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        Gamma.IsWarp (later W u)
  later_finite : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        Gamma.HasFiniteCharacter (later W u)
  later_in_roof : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        ∀ p ∈ later W u, p.support ⊆ C.outerRoof
  cut_boundary : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (X : Set V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
    C.persistent ⊆ C.newSlice →
    u ∈ W.realPart.terminals →
    initialSeed W u ⊆ X →
    #X ≤ kappa →
    HammockClosedUpTo Gamma Y X C.before C.innerRoof C.outerRoof kappa →
    LargeHammockClosed Gamma Y X C.before C.innerRoof C.outerRoof kappa →
    HasPreservingTargetPaths Gamma C.oldSlice X C.newSlice Preserves →
    ClosedUnderPaths Gamma Y X →
    ClosedUnderPaths Gamma (later W u) X →
    ContainedInRoof X C.outerRoof →
    OutsideCutBoundary (Y := Y) (later W u) X
      C.before C.innerRoof C.outerRoof

namespace LinkageFirstClubStageSeedSystem

variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- Specialize the selected club-stage data to one scheduler request. -/
def seed (S : LinkageFirstClubStageSeedSystem C)
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hu : u ∈ W.realPart.terminals) :
    LinkageFirstClosedCutSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  before := C.before
  innerRoof := C.innerRoof
  outerRoof := C.outerRoof
  targetSlice := C.oldSlice
  targetSide := C.newSlice
  initialSeed := S.initialSeed W u
  later := S.later W u
  Preserves := S.Preserves
  target_paths := S.target_paths
  reference_isWarp := S.reference_isWarp
  reference_finite := S.reference_finite
  reference_in_roof := S.reference_in_roof
  later_isWarp := S.later_isWarp W u hW hpersistent hu
  later_finite := S.later_finite W u hW hpersistent hu
  later_in_roof := S.later_in_roof W u hW hpersistent hu
  safe_in_roof := S.safe_in_roof
  kappa_infinite := C.capacity_infinite
  before_card := C.before_card
  initial_card := S.initial_card W u hW hpersistent hu
  initial_in_roof := S.initial_in_roof W u hW hpersistent hu
  cut_boundary := fun X hseed hcard hclosed hlarge htarget
      hreference hlater hroof ↦
    S.cut_boundary W u X hW hpersistent hu hseed hcard hclosed hlarge
      htarget hreference hlater hroof

/-- The ladder-specialized system supplies the repaired scheduler provider. -/
theorem seedProvider (S : LinkageFirstClubStageSeedSystem C) :
    LinkageFirstClosedCutSeedProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent := by
  intro W u hW hpersistent hu
  exact ⟨S.seed W u hW hpersistent hu⟩

/-- Run the linkage-first closure for every scheduler request. -/
theorem closedRequestProvider (S : LinkageFirstClubStageSeedSystem C) :
    ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent :=
  closedRequestProvider_of_linkageFirstSeedProvider S.seedProvider

/-- End-to-end stable successor compiler in the repaired dependency order.
The later linkage is chosen by `S`, the omega closure is performed by
`exists_closedRequest`, and the already checked club-stage union compiler
builds the single oriented global transaction. -/
theorem stable934Compiler_of_linkageFirstClubStageGeometry
    (S : LinkageFirstClubStageSeedSystem C)
    (U : ClubStageUnionSystem C) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      C.newSlice C.closedSet C.persistent Gamma.target := by
  exact stable934Compiler_of_globalFracturedSplice
    C.normalized S.reference_isWarp S.reference_finite
    S.closedRequestProvider
    (wholeFamilySpliceRelationCompiler_of_unionGeometry
      (wholeFamilyUnionGeometryCompiler_of_clubStage U))

/-- One concrete output of the repaired club-stage transaction, before the
terminal scheduler forgets how its successor was built.  The request,
simultaneous assignment, raw union relation, and oriented replacement are
kept in one dependent package.  This is the data needed to build the
monotone global run; `Stable934Compiler` alone intentionally erases it. -/
structure ResolvedSuccessor
    (S : LinkageFirstClubStageSeedSystem C)
    (U : ClubStageUnionSystem C)
    (W : LinkageBlueprint Gamma Y kappa) (u : V) where
  request : ClosedFracturedReplacementRequest
    (Gamma := Gamma) (Y := Y) (kappa := kappa) C.persistent
  data : ClubStageUnionData C W request.assignment u
  replacement : WholeFamilyOrientedReplacement W request.assignment u
    C.newSlice C.closedSet C.persistent Gamma.target
  orientation_edge : replacement.orientation.edge =
    data.inside ∪ assignedFiniteEdges request.assignment
  orientation_carrier : replacement.orientation.carrier = data.carrier

namespace ResolvedSuccessor

/-- The actual successor blueprint retained by a resolved transaction. -/
def result
    {S : LinkageFirstClubStageSeedSystem C}
    {U : ClubStageUnionSystem C}
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (R : ResolvedSuccessor S U W u) :
    LinkageBlueprint Gamma Y kappa :=
  R.replacement.result

/-- Claim 2 classifies the assignment already stored in the request, so a
resolved transaction has the exact stable-successor conclusion used by the
scheduler. -/
theorem stableExtensionConclusion
    {S : LinkageFirstClubStageSeedSystem C}
    {U : ClubStageUnionSystem C}
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (R : ResolvedSuccessor S U W u) :
    StableExtensionConclusion W R.result u C.newSlice C.closedSet
      C.persistent Gamma.target := by
  have hclassified := classify_simultaneousAssignment_of_closed
    (persistent := C.persistent) R.request.closed R.request.assignment
      R.request.assignment_closure
  exact R.replacement.stableExtensionConclusion hclassified.2

end ResolvedSuccessor

/-- Construct one fully retained successor transaction.  Unlike the
proposition-valued compiler, this theorem exposes the raw relation and its
carrier to the subsequent cofinal scheduler construction. -/
theorem exists_resolvedSuccessor
    (S : LinkageFirstClubStageSeedSystem C)
    (U : ClubStageUnionSystem C)
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hu : u ∈ W.realPart.terminals) :
    Nonempty (ResolvedSuccessor S U W u) := by
  let R := (S.closedRequestProvider W u hW hpersistent hu).some
  let A : SimultaneousAssignment R.fractured.paths Y := R.assignment
  have hclassified := classify_simultaneousAssignment_of_closed
    (persistent := C.persistent) R.closed A R.assignment_closure
  let D := (U W u hW hpersistent hu R A).some
  let G := D.toWholeFamilyUnionGeometry
  let Q := (G.spliceRelation hclassified.1).exists_orientedReplacement_exact
  exact ⟨{
    request := R
    data := D
    replacement := Q.choose
    orientation_edge := Q.choose_spec.1
    orientation_carrier := Q.choose_spec.2 }⟩

end LinkageFirstClubStageSeedSystem

end LinkageBlueprint
end Blueprint
end Erdos599
