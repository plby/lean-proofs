/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutFracturedProjection
import ErdosProblems.Erdos599.HalfwayClosedEndpointPairing
import ErdosProblems.Erdos599.HalfwayRowClosure
import ErdosProblems.Erdos599.HalfwayStageGeometry

/-!
# Closure-first Section 9 seed interface

The closing set in Assertions 9.22--9.25 is constructed before the family
`W ⇂ X` exists.  In particular a source-faithful seed must not demand a
simultaneous assignment, or its intersection-with-`X` proof, uniformly for
every arbitrary set `X`.

This file records the corrected dependency order.  The omega construction
first returns its unique closed set together with all seven conclusions of
Assertions 9.22--9.25.  A selected cut package is requested only at that
closed set.  The resulting package converts definitionally to the existing
global-replacement request, so downstream relation compilation is unchanged.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-! ## Post-closure first-hit replacement -/

/-- The exact source-specific operation still required after the ordinary
fractured assignment has been projected.

For every assigned path it chooses a safe path with the same initial and the
same optional terminal, but whose interior avoids the already constructed
closed set and which genuinely leaves it.  The shared terminal map is what
makes simultaneous finite-terminal injectivity automatic.  Unlike the false
generic implication from bracket safeness, this record states precisely the
first-hit/last-exit conclusion which the Section 9 cut argument must prove. -/
structure ClosedSetAvoidingReplacement
    {Z : Set Gamma.DPath}
    (A : SimultaneousAssignment Z Y) (X : Set V) where
  path : ∀ s : {x // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y},
    AltPath Gamma.graph
  starts_at : ∀ s, (path s).initial = s.1
  safe : ∀ s, IsSafe Y (path s)
  terminal_eq : ∀ s, (path s).terminal? = (A.assigned s).terminal?
  interior_disjoint_finite : ∀ s v,
    (path s).terminal? = some v →
      Disjoint (hammockInterior s.1 (.vertex v) (path s)) X
  interior_disjoint_infinite : ∀ s,
    (path s).IsInfinite →
      Disjoint (hammockInterior s.1 .infinity (path s)) X
  outside : ∀ s, ¬ (path s).vertexSet ⊆ X

namespace ClosedSetAvoidingReplacement

variable {Z : Set Gamma.DPath}
variable {A : SimultaneousAssignment Z Y} {X : Set V}

private theorem replacement_infinite_iff
    (R : ClosedSetAvoidingReplacement A X) (s) :
    (R.path s).IsInfinite ↔ (A.assigned s).IsInfinite := by
  rw [AltPath.isInfinite_iff_terminal?_eq_none,
    AltPath.isInfinite_iff_terminal?_eq_none, R.terminal_eq]

/-- Replace all assigned paths simultaneously while retaining the original
endpoint injection. -/
noncomputable def assignment (R : ClosedSetAvoidingReplacement A X) :
    SimultaneousAssignment Z Y where
  assigned := R.path
  starts_at := R.starts_at
  safe := R.safe
  leaving := by
    intro s
    rcases A.leaving s with hinfinite | ⟨v, hterm, hvY⟩
    · exact Or.inl ((R.replacement_infinite_iff s).2 hinfinite)
    · exact Or.inr ⟨v, (R.terminal_eq s).trans hterm, hvY⟩
  maximal := by
    intro s
    rcases A.maximal s with hinfinite | ⟨v, hv, hterm⟩
    · exact Or.inl ((R.replacement_infinite_iff s).2 hinfinite)
    · exact Or.inr ⟨v, hv, (R.terminal_eq s).trans hterm⟩
  finite_terminals_injective := by
    intro s t v hs ht
    apply A.finite_terminals_injective
    · rw [← R.terminal_eq s]
      exact hs
    · rw [← R.terminal_eq t]
      exact ht

/-- The first-hit/last-exit replacement is exactly enough to build the
selected outside assignment; eligibility is supplied separately by the cut
boundary when compiling `AssignmentClosureContext`. -/
def outsideAssignment
    {W : Set Gamma.DPath} {F : OutsideFracturedWarp W X}
    {A : SimultaneousAssignment F.holes.paths Y}
    (R : ClosedSetAvoidingReplacement A X) :
    OutsideAssignment (Y := Y) F := by
  let B := R.assignment
  refine {
    assignment := B
    finite_meets_closure := ?_
    infinite_meets_closure := ?_
    leaves_closure := R.outside }
  · intro s v hterm x hx
    by_contra hxend
    have hxInterior :
        x ∈ hammockInterior s.1 (.vertex v) (R.path s) := by
      refine ⟨hx.1, ?_⟩
      simpa [hammockEndpoints] using hxend
    exact Set.disjoint_left.1 (R.interior_disjoint_finite s v hterm)
      hxInterior hx.2
  · intro s hinfinite x hx
    by_contra hxend
    have hxInterior :
        x ∈ hammockInterior s.1 .infinity (R.path s) := by
      refine ⟨hx.1, ?_⟩
      simpa [hammockEndpoints] using hxend
    exact Set.disjoint_left.1 (R.interior_disjoint_infinite s hinfinite)
      hxInterior hx.2

end ClosedSetAvoidingReplacement

/-- The cut-dependent data selected after the closing set is known.  This is
exactly a `ClosedFracturedReplacementRequest` without duplicating the already
available `HammockClosedUpTo` proof. -/
structure SelectedClosedFracturedCut
    (X before innerRoof outerRoof : Set V) where
  fractured : FracturedWarp Gamma
  boundary_aligned : BoundaryAligned fractured.paths Y
  finite_character : Gamma.HasFiniteCharacter fractured.paths
  recombined_finite_character :
    Gamma.HasFiniteCharacter fractured.edgeWarp
  reference_initials :
    Gamma.initialSet Y ⊆ Gamma.initialSet fractured.paths
  assignment : SimultaneousAssignment fractured.paths Y
  assignment_closure :
    AssignmentClosureContext assignment X before innerRoof outerRoof

namespace SelectedClosedFracturedCut

/-- Reattach the omega-closure certificate after the cut-dependent selection
has been performed. -/
def toClosedFracturedReplacementRequest
    {X before innerRoof outerRoof persistent : Set V}
    (D : SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    ClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent where
  fractured := D.fractured
  closureSet := X
  before := before
  innerRoof := innerRoof
  outerRoof := outerRoof
  boundary_aligned := D.boundary_aligned
  finite_character := D.finite_character
  recombined_finite_character := D.recombined_finite_character
  reference_initials := D.reference_initials
  assignment := D.assignment
  closed := hclosed
  assignment_closure := D.assignment_closure

/-- An already constructed literal outside cut supplies the selected package
without any arbitrary-`X` quantification. -/
def ofOutsideCutConstruction
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (D : OutsideCutConstruction
      (Gamma := Gamma) (Y := Y) W X before innerRoof outerRoof) :
    SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof where
  fractured := D.fractured
  boundary_aligned := D.boundaryAligned
  finite_character := D.finiteCharacter
  recombined_finite_character := D.edgeWarpFiniteCharacter
  reference_initials := D.referenceInitials
  assignment := D.assignment
  assignment_closure := D.assignmentClosure

/-- Construct all path-level cut geometry from the actual row.  The only
remaining inputs are the two genuinely source-specific facts: the boundary
of this closed slice and one selected assignment with the required
closed-set avoidance. -/
theorem exists_of_literalOutsideCut
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (boundary : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (assigned : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideAssignment (Y := Y) F.outside) :
    Nonempty (SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp W X hW hfinite
  let D : OutsideCutConstruction
      (Gamma := Gamma) (Y := Y) W X before innerRoof outerRoof := {
    outside := F.outside
    boundary := boundary F
    assigned := assigned F }
  exact ⟨ofOutsideCutConstruction D⟩

/-- First-hit form of the literal cut constructor.  An ordinary projected
assignment is not required to avoid `X`; the source-specific replacement
does so while preserving its endpoint map, and therefore preserves the
simultaneous assignment axioms automatically. -/
theorem exists_of_literalOutsideCut_and_avoidingReplacement
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (boundary : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (baseAssignment : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      SimultaneousAssignment F.outside.holes.paths Y)
    (avoid : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      ClosedSetAvoidingReplacement (baseAssignment F) X) :
    Nonempty (SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof) := by
  apply exists_of_literalOutsideCut hW hfinite boundary
  intro F
  exact (avoid F).outsideAssignment

end SelectedClosedFracturedCut

/-! ## Source-faithful endpoint output

The paper uses the fractured assignment only through its injective endpoint
matching and the Claim-2 classification of those endpoints.  Asking for a
new simultaneous assignment whose whole paths avoid `X` is stronger and is
not a consequence of Theorem 4.12.  The following package is therefore the
literal post-closure output needed by Assertion 9.31. -/

/-- The cut-dependent endpoint matching selected after the closing set is
known.  Unlike `SelectedClosedFracturedCut`, it does not assert that the
Claim-2 witnesses form a simultaneous family of maximal paths. -/
structure SelectedClosedEndpointCut
    (X before innerRoof outerRoof : Set V) where
  fractured : FracturedWarp Gamma
  finite_character : Gamma.HasFiniteCharacter fractured.paths
  recombined_finite_character :
    Gamma.HasFiniteCharacter fractured.edgeWarp
  reference_initials :
    Gamma.initialSet Y ⊆ Gamma.initialSet fractured.paths
  pairing : ClosedEndpointPairing
    (Gamma := Gamma) (Y := Y) fractured X before innerRoof outerRoof

/-- A closed endpoint-pairing request.  This is the source-faithful analogue
of `ClosedFracturedReplacementRequest`: it retains exactly the data used
after Assertion 9.31 and carries the already constructed omega-closure
certificate. -/
structure ClosedEndpointReplacementRequest (persistent : Set V) where
  fractured : FracturedWarp Gamma
  closureSet : Set V
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  finite_character : Gamma.HasFiniteCharacter fractured.paths
  recombined_finite_character :
    Gamma.HasFiniteCharacter fractured.edgeWarp
  reference_initials :
    Gamma.initialSet Y ⊆ Gamma.initialSet fractured.paths
  pairing : ClosedEndpointPairing
    (Gamma := Gamma) (Y := Y) fractured closureSet
      before innerRoof outerRoof
  closed : HammockClosedUpTo Gamma Y closureSet
    before innerRoof outerRoof kappa

namespace SelectedClosedEndpointCut

/-- Reattach the omega-closure certificate after the endpoint pairing has
been selected at the unique closed set. -/
def toClosedEndpointReplacementRequest
    {X before innerRoof outerRoof persistent : Set V}
    (D : SelectedClosedEndpointCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    ClosedEndpointReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent where
  fractured := D.fractured
  closureSet := X
  before := before
  innerRoof := innerRoof
  outerRoof := outerRoof
  finite_character := D.finite_character
  recombined_finite_character := D.recombined_finite_character
  reference_initials := D.reference_initials
  pairing := D.pairing
  closed := hclosed

/-- Construct the literal fractured part unconditionally from the later
finite-character linkage.  Once the actual slice boundary is supplied, the
only remaining source theorem is the X-endpoint-split pairing itself. -/
theorem exists_of_literalOutsideCut_and_pairing
    {W : Set Gamma.DPath} {X before innerRoof outerRoof : Set V}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (boundary : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (pairing : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      ClosedEndpointPairing (Gamma := Gamma) (Y := Y)
        F.outside.holes X before innerRoof outerRoof) :
    Nonempty (SelectedClosedEndpointCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp W X hW hfinite
  exact ⟨{
    fractured := F.outside.holes
    finite_character := F.outside.finiteCharacter
    recombined_finite_character := F.outside.edgeWarpFiniteCharacter
    reference_initials :=
      (boundary F).fractured_referenceInitials F.outside
    pairing := pairing F }⟩

end SelectedClosedEndpointCut

/-- Source-order seed whose selected output is the minimal Claim-2-certified
endpoint matching.  The closure family is the earlier slice-difference
family; in particular it is not the later linkage which is fractured. -/
structure ClosureFirstEndpointSeed where
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  targetSlice : Set V
  targetSide : Set V
  initialSeed : Set V
  closureFamily : Set Gamma.DPath
  Preserves : FinitePath Gamma.graph → Prop
  target_paths : ∀ v ∈ targetSlice ∩ outerRoof,
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ targetSide ∧
        p.support ⊆ outerRoof ∧ Preserves p
  reference_isWarp : Gamma.IsWarp Y
  closureFamily_isWarp : Gamma.IsWarp closureFamily
  reference_in_roof : ∀ p ∈ Y, p.support ⊆ outerRoof
  closureFamily_in_roof : ∀ p ∈ closureFamily,
    p.support ⊆ outerRoof
  safe_in_roof : EligibleHammocksContainedInRoof Gamma Y
    before innerRoof outerRoof
  kappa_infinite : aleph0 ≤ kappa
  before_card : #before ≤ kappa
  initial_card : #initialSeed ≤ kappa
  initial_in_roof : initialSeed ⊆ outerRoof
  selected_cut : ∀ X : Set V,
    initialSeed ⊆ X →
    #X ≤ kappa →
    HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa →
    LargeHammockClosed Gamma Y X before innerRoof outerRoof kappa →
    HasPreservingTargetPaths Gamma targetSlice X targetSide Preserves →
    ClosedUnderPaths Gamma Y X →
    ClosedUnderPaths Gamma closureFamily X →
    ContainedInRoof X outerRoof →
    Nonempty (SelectedClosedEndpointCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof)

namespace ClosureFirstEndpointSeed

/-- Run Assertions 9.22--9.25 first and select the endpoint pairing only at
their resulting closed set. -/
theorem exists_closedEndpointRequest
    {persistent : Set V}
    (S : ClosureFirstEndpointSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) :
    Nonempty (ClosedEndpointReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, htarget,
      hreference, hfamily, hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_rowClosure Gamma Y S.closureFamily
      kappa kappa S.before S.innerRoof S.outerRoof S.targetSlice
      S.targetSide S.initialSeed S.Preserves S.target_paths
      S.reference_isWarp S.closureFamily_isWarp S.reference_in_roof
      S.closureFamily_in_roof S.safe_in_roof S.kappa_infinite
      (le_refl kappa) S.before_card S.initial_card S.initial_in_roof
  obtain ⟨D⟩ := S.selected_cut X hseed hcard hclosed hlarge htarget
    hreference hfamily hroof
  exact ⟨D.toClosedEndpointReplacementRequest hclosed⟩

end ClosureFirstEndpointSeed

/-- Scheduler-facing source of closure-first endpoint seeds. -/
def ClosureFirstEndpointSeedProvider
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        Nonempty (ClosureFirstEndpointSeed
          (Gamma := Gamma) (Y := Y) (kappa := kappa))

/-- Scheduler-facing source of the closed endpoint requests themselves. -/
def ClosedEndpointReplacementRequestProvider
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        Nonempty (ClosedEndpointReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent)

theorem closedEndpointRequestProvider_of_closureFirstEndpointSeedProvider
    {T Z persistent : Set V}
    (hseed : ClosureFirstEndpointSeedProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    ClosedEndpointReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u hW hpersistent hu
  exact (hseed W u hW hpersistent hu).some.exists_closedEndpointRequest

/-- Source data whose dependencies follow Assertions 9.22--9.31 literally.

`selected_cut` is invoked only after `X` has all the conclusions of the
omega closing-up theorem.  This replaces the unsound interface consisting
of independent functions `fractured X`, `assignment X`, and
`assignment_closure X` on every set `X`. -/
structure ClosureFirstReplacementSeed where
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  targetSlice : Set V
  targetSide : Set V
  initialSeed : Set V
  /-- The earlier symmetric-difference/layer family under which the source
  closes `X`.  It is deliberately not the later linkage which is fractured:
  paths of that linkage may enter and leave `X`. -/
  closureFamily : Set Gamma.DPath
  Preserves : FinitePath Gamma.graph → Prop
  target_paths : ∀ v ∈ targetSlice ∩ outerRoof,
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ targetSide ∧
        p.support ⊆ outerRoof ∧ Preserves p
  reference_isWarp : Gamma.IsWarp Y
  closureFamily_isWarp : Gamma.IsWarp closureFamily
  reference_in_roof : ∀ p ∈ Y, p.support ⊆ outerRoof
  closureFamily_in_roof : ∀ p ∈ closureFamily, p.support ⊆ outerRoof
  safe_in_roof : EligibleHammocksContainedInRoof Gamma Y
    before innerRoof outerRoof
  kappa_infinite : aleph0 ≤ kappa
  before_card : #before ≤ kappa
  initial_card : #initialSeed ≤ kappa
  initial_in_roof : initialSeed ⊆ outerRoof
  selected_cut : ∀ X : Set V,
    initialSeed ⊆ X →
    #X ≤ kappa →
    HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa →
    LargeHammockClosed Gamma Y X before innerRoof outerRoof kappa →
    HasPreservingTargetPaths Gamma targetSlice X targetSide Preserves →
    ClosedUnderPaths Gamma Y X →
    ClosedUnderPaths Gamma closureFamily X →
    ContainedInRoof X outerRoof →
    Nonempty (SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof)

namespace ClosureFirstReplacementSeed

/-- Run the omega closure and only then select the literal cut assignment. -/
theorem exists_closedRequest
    {persistent : Set V}
    (S : ClosureFirstReplacementSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) :
    Nonempty (ClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, htarget,
      hreference, hrow, hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_rowClosure Gamma Y S.closureFamily
      kappa kappa S.before
      S.innerRoof S.outerRoof S.targetSlice S.targetSide S.initialSeed
      S.Preserves S.target_paths S.reference_isWarp S.closureFamily_isWarp
      S.reference_in_roof S.closureFamily_in_roof S.safe_in_roof
      S.kappa_infinite (le_refl kappa) S.before_card S.initial_card
      S.initial_in_roof
  obtain ⟨D⟩ := S.selected_cut X hseed hcard hclosed hlarge htarget
    hreference hrow hroof
  exact ⟨D.toClosedFracturedReplacementRequest hclosed⟩

end ClosureFirstReplacementSeed

/-- Scheduler provider using the corrected closure-first dependency order. -/
def ClosureFirstReplacementSeedProvider
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        Nonempty (ClosureFirstReplacementSeed
          (Gamma := Gamma) (Y := Y) (kappa := kappa))

/-- The corrected seed provider feeds the existing global transaction
compiler without changing its request type. -/
theorem closedRequestProvider_of_closureFirstSeedProvider
    {T Z persistent : Set V}
    (hseed : ClosureFirstReplacementSeedProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u hW hpersistent hu
  exact (hseed W u hW hpersistent hu).some.exists_closedRequest

/-! ## Ladder-specialized corrected seed -/

/-- Club-stage data in source order, with the Claim-2 endpoint matching as
the selected post-closure output.  `target_paths` ends on the arbitrary next
slice `C.newSlice`; it is not hard-coded to the ambient web target. -/
structure ClosureFirstEndpointClubStageSeedSystem
    (C : ClubStageGeometry Gamma Y kappa theta) where
  Preserves : FinitePath Gamma.graph → Prop
  target_paths : ∀ v ∈ C.oldSlice ∩ C.outerRoof,
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ C.newSlice ∧
        p.support ⊆ C.outerRoof ∧ Preserves p
  reference_isWarp : Gamma.IsWarp Y
  reference_in_roof : ∀ p ∈ Y, p.support ⊆ C.outerRoof
  safe_in_roof : EligibleHammocksContainedInRoof Gamma Y
    C.before C.innerRoof C.outerRoof
  initialSeed : LinkageBlueprint Gamma Y kappa → V → Set V
  closureFamily : LinkageBlueprint Gamma Y kappa → V → Set Gamma.DPath
  initial_card : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        #(initialSeed W u) ≤ kappa
  initial_in_roof : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        initialSeed W u ⊆ C.outerRoof
  closureFamily_isWarp : ∀
      (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        Gamma.IsWarp (closureFamily W u)
  closureFamily_in_roof : ∀
      (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        ∀ p ∈ closureFamily W u, p.support ⊆ C.outerRoof
  selected_cut : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
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
    ClosedUnderPaths Gamma (closureFamily W u) X →
    ContainedInRoof X C.outerRoof →
    Nonempty (SelectedClosedEndpointCut
      (Gamma := Gamma) (Y := Y) X C.before C.innerRoof C.outerRoof)

namespace ClosureFirstEndpointClubStageSeedSystem

variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- Specialize one club-stage scheduler request. -/
def seed (S : ClosureFirstEndpointClubStageSeedSystem C)
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hu : u ∈ W.realPart.terminals) :
    ClosureFirstEndpointSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  before := C.before
  innerRoof := C.innerRoof
  outerRoof := C.outerRoof
  targetSlice := C.oldSlice
  targetSide := C.newSlice
  initialSeed := S.initialSeed W u
  closureFamily := S.closureFamily W u
  Preserves := S.Preserves
  target_paths := S.target_paths
  reference_isWarp := S.reference_isWarp
  closureFamily_isWarp := S.closureFamily_isWarp W u hW hpersistent hu
  reference_in_roof := S.reference_in_roof
  closureFamily_in_roof := S.closureFamily_in_roof W u hW hpersistent hu
  safe_in_roof := S.safe_in_roof
  kappa_infinite := C.capacity_infinite
  before_card := C.before_card
  initial_card := S.initial_card W u hW hpersistent hu
  initial_in_roof := S.initial_in_roof W u hW hpersistent hu
  selected_cut := fun X hseed hcard hclosed hlarge htarget
      hreference hfamily hroof ↦
    S.selected_cut W u X hW hpersistent hu hseed hcard hclosed hlarge
      htarget hreference hfamily hroof

theorem seedProvider (S : ClosureFirstEndpointClubStageSeedSystem C) :
    ClosureFirstEndpointSeedProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent := by
  intro W u hW hpersistent hu
  exact ⟨S.seed W u hW hpersistent hu⟩

theorem closedEndpointRequestProvider
    (S : ClosureFirstEndpointClubStageSeedSystem C) :
    ClosedEndpointReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent :=
  closedEndpointRequestProvider_of_closureFirstEndpointSeedProvider
    S.seedProvider

end ClosureFirstEndpointClubStageSeedSystem

/-- A club-stage seed with the closure/cut dependency in the source order.
All slice and roof parameters are definitionally those of `C`. -/
structure ClosureFirstClubStageSeedSystem
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
  /-- Earlier slice symmetric-difference/layer family; never instantiate this
  with the later linkage which is cut after closure. -/
  closureFamily : LinkageBlueprint Gamma Y kappa → V → Set Gamma.DPath
  initial_card : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        #(initialSeed W u) ≤ kappa
  initial_in_roof : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        initialSeed W u ⊆ C.outerRoof
  closureFamily_isWarp : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        Gamma.IsWarp (closureFamily W u)
  closureFamily_in_roof : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
        ∀ p ∈ closureFamily W u, p.support ⊆ C.outerRoof
  selected_cut : ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
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
    ClosedUnderPaths Gamma (closureFamily W u) X →
    ContainedInRoof X C.outerRoof →
    Nonempty (SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X C.before C.innerRoof C.outerRoof)

namespace ClosureFirstClubStageSeedSystem

variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- Specialize one scheduler request while retaining the post-closure cut
selection as a dependent function. -/
def seed (S : ClosureFirstClubStageSeedSystem C)
    (W : LinkageBlueprint Gamma Y kappa) (u : V)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hu : u ∈ W.realPart.terminals) :
    ClosureFirstReplacementSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  before := C.before
  innerRoof := C.innerRoof
  outerRoof := C.outerRoof
  targetSlice := C.oldSlice
  targetSide := C.newSlice
  initialSeed := S.initialSeed W u
  closureFamily := S.closureFamily W u
  Preserves := S.Preserves
  target_paths := S.target_paths
  reference_isWarp := S.reference_isWarp
  closureFamily_isWarp := S.closureFamily_isWarp W u hW hpersistent hu
  reference_in_roof := S.reference_in_roof
  closureFamily_in_roof := S.closureFamily_in_roof W u hW hpersistent hu
  safe_in_roof := S.safe_in_roof
  kappa_infinite := C.capacity_infinite
  before_card := C.before_card
  initial_card := S.initial_card W u hW hpersistent hu
  initial_in_roof := S.initial_in_roof W u hW hpersistent hu
  selected_cut := fun X hseed hcard hclosed hlarge htarget
      hreference hrow hroof ↦
    S.selected_cut W u X hW hpersistent hu hseed hcard hclosed hlarge
      htarget hreference hrow hroof

theorem seedProvider (S : ClosureFirstClubStageSeedSystem C) :
    ClosureFirstReplacementSeedProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent := by
  intro W u hW hpersistent hu
  exact ⟨S.seed W u hW hpersistent hu⟩

/-- Existing global replacement theorems consume this adapter. -/
theorem closedRequestProvider (S : ClosureFirstClubStageSeedSystem C) :
    ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      C.newSlice C.closedSet C.persistent :=
  closedRequestProvider_of_closureFirstSeedProvider S.seedProvider

/-- End-to-end successor compiler using the corrected closure-first seed and
the existing concrete union system.  No arbitrary-set assignment or closure
proof is introduced by this adapter. -/
theorem stable934Compiler_of_closureFirstClubStageGeometry
    (S : ClosureFirstClubStageSeedSystem C)
    (U : ClubStageUnionSystem C) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      C.newSlice C.closedSet C.persistent Gamma.target := by
  exact stable934Compiler_of_globalFracturedSplice
    C.normalized S.reference_isWarp S.reference_finite
    S.closedRequestProvider
    (wholeFamilySpliceRelationCompiler_of_unionGeometry
      (wholeFamilyUnionGeometryCompiler_of_clubStage U))

end ClosureFirstClubStageSeedSystem

end LinkageBlueprint
end Blueprint
end Erdos599
