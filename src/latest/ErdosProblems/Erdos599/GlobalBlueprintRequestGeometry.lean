/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintRequestProvider

/-!
# Geometry carried by a scheduled global replacement request

The simultaneous-assignment interface used by `ClosedFracturedReplacementRequest`
requires every initial vertex of the fractured family to lie in the ambient
source `Gamma.source`.  Consequently a scheduled slice endpoint cannot in
general be made an uncovered assignment source: the endpoint belongs to the
source of an auxiliary slice/quotient web, not necessarily to the source of
the ambient web.

This file records that obstruction as a theorem and isolates the part of an
honest scheduled request which *is* supplied by the existing omega-closure
construction.  The scheduled endpoint is put in the closed set and receives
a closed-set-contained path to `B`; the construction of the fractured outside
family and the assignment-disjointness facts remains a separate input.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open Alternating DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-! ## The ambient-source obstruction -/

/-- Every vertex placed in the assignment domain by the proposed scheduled
request is necessarily an ambient source.  This is the exact incompatibility
with an internal ladder-slice endpoint. -/
theorem ScheduledClosedFracturedReplacementRequest.scheduled_mem_source
    {W : LinkageBlueprint Gamma Y kappa} {u : V} {persistent : Set V}
    (R : ScheduledClosedFracturedReplacementRequest W u persistent) :
    u ∈ Gamma.source :=
  R.request.source_side R.scheduled_uncovered.1

/-- A non-source slice endpoint cannot be represented by the scheduled
assignment-domain strengthening. -/
theorem not_nonempty_scheduledClosedFracturedReplacementRequest_of_not_mem_source
    {W : LinkageBlueprint Gamma Y kappa} {u : V} {persistent : Set V}
    (hu : u ∉ Gamma.source) :
    ¬ Nonempty (ScheduledClosedFracturedReplacementRequest W u persistent) := by
  rintro ⟨R⟩
  exact hu R.scheduled_mem_source

/-- One legitimate scheduled terminal outside the ambient source refutes a
uniform provider of assignment-domain scheduled requests. -/
theorem not_scheduledClosedFracturedReplacementRequestProvider_of_terminal_not_mem_source
    {T Z persistent : Set V} {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hpersistent : persistent ⊆ T)
    (huterminal : u ∈ W.realPart.terminals)
    (husource : u ∉ Gamma.source) :
    ¬ ScheduledClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro hprovider
  exact
    (not_nonempty_scheduledClosedFracturedReplacementRequest_of_not_mem_source
      (W := W) (persistent := persistent) husource)
      (hprovider W u hW hpersistent huterminal)

/-- The canonical honest-reference request has no uncovered initial vertex,
so it cannot supply the assignment-domain scheduled witness for any vertex. -/
@[simp] theorem honestFracturedWarp_uncoveredInitials_eq_empty
    (hYwarp : Gamma.IsWarp Y) :
    Gamma.initialSet (honestFracturedWarp hYwarp).paths \
      Gamma.initialSet Y = ∅ := by
  simp

/-! ## The source-faithful scheduled closure stage -/

/-! ### Closing simultaneously under an additional slice family

The closure used in Assertion 9.31 is not merely closed under the reference
warp.  It is also closed under the path family encoding the symmetric
difference of the two relevant ladder slices.  The basic 9.22--9.25 closure
operator predates that application and only includes `Y`.  The following
variant inserts the second family in the same omega iteration.  This is
important: closing under it only after the hammock construction would lose
the maximal-hammock closure at newly inserted vertices. -/

/-- One 9.22--9.25 closing step, followed in the same stage by all members
of `F` meeting the current set. -/
def scheduledClosingStepWithExtra
    (Gamma : DWeb V) (Y F : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) : Set V :=
  closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X ∪
    meetingVertices Gamma F X

theorem subset_scheduledClosingStepWithExtra
    (Gamma : DWeb V) (Y F : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) :
    X ⊆ scheduledClosingStepWithExtra Gamma Y F rho ZBefore innerRoof roof
      T B Preserves hTarget X :=
  fun _ hx ↦ Or.inl (subset_closingStep Gamma Y rho ZBefore innerRoof roof
    T B Preserves hTarget X hx)

private theorem mk_union_le_current
    {A B : Set V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hA : #A ≤ kappa) (hB : #B ≤ kappa) :
    #(A ∪ B : Set V) ≤ kappa :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le hkappa hA hB)

theorem mk_scheduledClosingStepWithExtra_le
    (Gamma : DWeb V) (Y F : Set Gamma.DPath)
    {rho kappa : Cardinal.{u}} (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y) (hF : Gamma.IsWarp F)
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa) (X : Set V) (hX : #X ≤ kappa) :
    #(scheduledClosingStepWithExtra Gamma Y F rho ZBefore innerRoof roof
      T B Preserves hTarget X) ≤ kappa := by
  apply mk_union_le_current hkappa
  · exact mk_closingStep_le Gamma Y ZBefore innerRoof roof T B Preserves
      hTarget hY hkappa hrho hZBefore X hX
  · exact mk_meetingVertices_le Gamma F X hF hkappa hX

theorem scheduledClosingStepWithExtra_subset_roof
    (Gamma : DWeb V) (Y F : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hSafeRoof : ∀ Q : AltPath Gamma.graph,
      IsSafe Y Q → Q.vertexSet ⊆ roof)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hFroof : ∀ p ∈ F, p.support ⊆ roof)
    (X : Set V) (hX : X ⊆ roof) :
    scheduledClosingStepWithExtra Gamma Y F rho ZBefore innerRoof roof
      T B Preserves hTarget X ⊆ roof := by
  rintro x (hx | hx)
  · exact closingStep_subset_roof Gamma Y rho ZBefore innerRoof roof T B
      Preserves hTarget hSafeRoof hYroof X hX hx
  · exact meetingVertices_subset_roof Gamma F X roof hFroof hx

/-- Assertions 9.22--9.25 with the additional path closure actually used by
Assertion 9.31.  Both closures are constructed, rather than accepted as
fields of a downstream request. -/
theorem exists_assertions_9_22_to_9_25_with_extra_paths
    (Gamma : DWeb V) (Y F : Set Gamma.DPath)
    (rho kappa : Cardinal.{u})
    (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y) (hF : Gamma.IsWarp F)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hFroof : ∀ p ∈ F, p.support ⊆ roof)
    (hSafeRoof : ∀ Q : AltPath Gamma.graph,
      IsSafe Y Q → Q.vertexSet ⊆ roof)
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa) (hX0roof : X0 ⊆ roof) :
    ∃ X : Set V,
      X0 ⊆ X ∧ #X ≤ kappa ∧
      HammockClosedUpTo Gamma Y X ZBefore innerRoof roof rho ∧
      LargeHammockClosed Gamma Y X ZBefore innerRoof roof rho ∧
      HasPreservingTargetPaths Gamma T X B Preserves ∧
      ClosedUnderPaths Gamma Y X ∧ ClosedUnderPaths Gamma F X ∧
      ContainedInRoof X roof := by
  let step : Set V → Set V :=
    scheduledClosingStepWithExtra Gamma Y F rho ZBefore innerRoof roof T B
      Preserves hTarget
  let X : Set V := omegaClosure step X0
  have hstageCard : ∀ n, #(closureStage step X0 n) ≤ kappa := by
    apply mk_closureStage_le hX0card
    intro S hS
    exact mk_scheduledClosingStepWithExtra_le Gamma Y F ZBefore innerRoof
      roof T B Preserves hTarget hY hF hkappa hrho hZBefore S hS
  have hstageRoof : ∀ n, closureStage step X0 n ⊆ roof := by
    apply closureStage_subset_roof hX0roof
    intro S hS
    exact scheduledClosingStepWithExtra_subset_roof Gamma Y F rho ZBefore
      innerRoof roof T B Preserves hTarget hSafeRoof hYroof hFroof S hS
  have hXroof : X ⊆ roof := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    exact hstageRoof n hxn
  refine ⟨X, closureStage_subset_omegaClosure step X0 0, ?_, ?_, ?_, ?_,
    ?_, ?_, hXroof⟩
  · change #(⋃ n, closureStage step X0 n) ≤ kappa
    let stages : ULift.{u} ℕ → Set V :=
      fun n ↦ closureStage step X0 n.down
    have heq : (⋃ n, closureStage step X0 n) = ⋃ i, stages i := by
      ext x
      simp [stages]
    rw [heq]
    refine (Cardinal.mk_iUnion_le stages).trans ?_
    apply Cardinal.mul_le_of_le hkappa
    · simpa [Cardinal.mk_nat] using hkappa
    · apply ciSup_le
      intro i
      exact hstageCard i.down
  · intro u e helig
    let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
    refine ⟨chosenHammock Gamma Y rho q,
      chosenHammock_spec Gamma Y rho q, ?_⟩
    have hclosing :
        closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves
            hTarget X0 ⊆ step X0 := by
      intro x hx
      exact Or.inl hx
    exact (chosenHammock_contained_all Gamma Y rho q).trans
      ((allHammockVertices_subset_closingStep Gamma Y rho ZBefore
        innerRoof roof T B Preserves hTarget X0).trans
        (hclosing.trans (closureStage_subset_omegaClosure step X0 1)))
  · intro u e helig hlarge
    let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
    refine ⟨chosenHammock Gamma Y rho q,
      (chosenHammock_spec Gamma Y rho q).isHammock,
      chosenHammock_card_eq_of_hasHammockCard Gamma Y rho q hlarge, ?_⟩
    have hclosing :
        closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves
            hTarget X0 ⊆ step X0 := by
      intro x hx
      exact Or.inl hx
    exact (chosenHammock_contained_all Gamma Y rho q).trans
      ((allHammockVertices_subset_closingStep Gamma Y rho ZBefore
        innerRoof roof T B Preserves hTarget X0).trans
        (hclosing.trans (closureStage_subset_omegaClosure step X0 1)))
  · intro v hv
    have hvRoof : v ∈ roof := hXroof hv.2
    let tv : TargetVertex T roof := ⟨v, hv.1, hvRoof⟩
    let p := targetChoice Gamma T roof B Preserves hTarget tv
    obtain ⟨n, hvn⟩ := Set.mem_iUnion.1 hv.2
    have hpSupport : p.support ⊆ X := by
      have hpTarget : p.support ⊆
          targetVertices Gamma T roof B Preserves hTarget
            (closureStage step X0 n) := by
        intro x hx
        exact Set.mem_iUnion.2 ⟨⟨tv, hvn⟩, hx⟩
      have hclosing :
          closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves
              hTarget (closureStage step X0 n) ⊆
            step (closureStage step X0 n) := by
        intro x hx
        exact Or.inl hx
      exact hpTarget.trans
        ((targetVertices_subset_closingStep Gamma Y rho ZBefore innerRoof
          roof T B Preserves hTarget (closureStage step X0 n)).trans
          (hclosing.trans
            (closureStage_subset_omegaClosure step X0 (n + 1))))
    exact ⟨p, (targetChoice_spec Gamma T roof B Preserves hTarget tv).1,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.1,
      hpSupport,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.2.2⟩
  · intro p hpY hpMeet
    obtain ⟨x, hxp, hxX⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxX
    have hclosing :
        closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves
            hTarget (closureStage step X0 n) ⊆
          step (closureStage step X0 n) := by
      intro w hw
      exact Or.inl hw
    exact (support_subset_meetingVertices Gamma Y (closureStage step X0 n)
      hpY ⟨x, hxp, hxn⟩).trans
        ((meetingVertices_subset_closingStep Gamma Y rho ZBefore innerRoof
          roof T B Preserves hTarget (closureStage step X0 n)).trans
          (hclosing.trans
            (closureStage_subset_omegaClosure step X0 (n + 1))))
  · intro p hpF hpMeet
    obtain ⟨x, hxp, hxX⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxX
    have hmeeting :
        meetingVertices Gamma F (closureStage step X0 n) ⊆
          step (closureStage step X0 n) := by
      intro w hw
      exact Or.inr hw
    exact (support_subset_meetingVertices Gamma F (closureStage step X0 n)
      hpF ⟨x, hxp, hxn⟩).trans
        (hmeeting.trans
          (closureStage_subset_omegaClosure step X0 (n + 1)))

/-- The part of a scheduled 9.31 request constructed by Assertions
9.22--9.25.  The scheduled endpoint belongs to the closed set, rather than
being incorrectly declared an ambient source of the fractured family. -/
structure ScheduledClosureRequest
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (z : V) (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop) where
  closureSet : Set V
  seed_subset : X0 ⊆ closureSet
  card_closure : #closureSet ≤ kappa
  hammock_closed :
    HammockClosedUpTo Gamma Y closureSet ZBefore innerRoof roof kappa
  large_hammock_closed :
    LargeHammockClosed Gamma Y closureSet ZBefore innerRoof roof kappa
  target_paths :
    HasPreservingTargetPaths Gamma T closureSet B Preserves
  reference_closed : ClosedUnderPaths Gamma Y closureSet
  contained_in_roof : ContainedInRoof closureSet roof
  scheduled_mem : z ∈ closureSet

/-- A scheduled closure which is simultaneously closed under the additional
path family used to encode the difference of the two ladder slices in
Assertion 9.31.  This is stronger than attaching `extra_closed` afterward:
the extra paths participate in every stage of the omega closure, so hammock
closure is also rerun at the vertices which they insert. -/
structure ScheduledClosureRequestWithExtraPaths
    (Gamma : DWeb V) (Y F : Set Gamma.DPath) (kappa : Cardinal.{u})
    (z : V) (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    extends ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves where
  extra_closed : ClosedUnderPaths Gamma F closureSet

/-- Forgetting the second closure recovers the ordinary scheduled request
consumed by the existing 9.31 interfaces. -/
abbrev ScheduledClosureRequestWithExtraPaths.base
    {Gamma : DWeb V} {Y F : Set Gamma.DPath} {kappa : Cardinal.{u}}
    {z : V} {ZBefore innerRoof roof T B X0 : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequestWithExtraPaths Gamma Y F kappa z ZBefore
      innerRoof roof T B X0 Preserves) :
    ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof T B X0
      Preserves :=
  C.toScheduledClosureRequest

/-- Construct the scheduled request with the slice-difference closure from
the same omega iteration as Assertions 9.22--9.25. -/
theorem exists_scheduledClosureRequestWithExtraPaths
    (Gamma : DWeb V) (Y F : Set Gamma.DPath) (kappa : Cardinal.{u})
    (z : V) (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hzseed : z ∈ X0)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y) (hF : Gamma.IsWarp F)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hFroof : ∀ p ∈ F, p.support ⊆ roof)
    (hSafeRoof : ∀ Q : AltPath Gamma.graph,
      IsSafe Y Q → Q.vertexSet ⊆ roof)
    (hkappa : aleph0 ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa) (hX0roof : X0 ⊆ roof) :
    Nonempty (ScheduledClosureRequestWithExtraPaths Gamma Y F kappa z
      ZBefore innerRoof roof T B X0 Preserves) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, hpaths, hreference, hextra,
      hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_extra_paths Gamma Y F kappa kappa
      ZBefore innerRoof roof T B X0 Preserves hTarget hY hF hYroof hFroof
      hSafeRoof hkappa le_rfl hZBefore hX0card hX0roof
  exact ⟨{
    closureSet := X
    seed_subset := hseed
    card_closure := hcard
    hammock_closed := hclosed
    large_hammock_closed := hlarge
    target_paths := hpaths
    reference_closed := hreference
    contained_in_roof := hroof
    scheduled_mem := hseed hzseed
    extra_closed := hextra }⟩

/-- The existing omega-closure theorem constructs the scheduled closure
stage whenever the seed already contains the scheduled endpoint. -/
theorem exists_scheduledClosureRequest
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (z : V) (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hzseed : z ∈ X0)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hSafeRoof : ∀ Q : AltPath Gamma.graph,
      IsSafe Y Q → Q.vertexSet ⊆ roof)
    (hkappa : aleph0 ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa) (hX0roof : X0 ⊆ roof) :
    Nonempty (ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof
      roof T B X0 Preserves) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, hpaths, hreference, hroof⟩ :=
    exists_assertions_9_22_to_9_25 Gamma Y kappa kappa ZBefore innerRoof
      roof T B X0 Preserves hTarget hY hYroof hSafeRoof hkappa le_rfl
      hZBefore hX0card hX0roof
  exact ⟨{
    closureSet := X
    seed_subset := hseed
    card_closure := hcard
    hammock_closed := hclosed
    large_hammock_closed := hlarge
    target_paths := hpaths
    reference_closed := hreference
    contained_in_roof := hroof
    scheduled_mem := hseed hzseed }⟩

/-- Membership of the scheduled endpoint in the current slice turns the
closure certificate into the required closed-set-contained `z`--`B` path. -/
theorem ScheduledClosureRequest.exists_scheduled_target_path
    {z : V} {ZBefore innerRoof roof T B X0 : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves)
    (hzT : z ∈ T) :
    ∃ p : FinitePath Gamma.graph,
      p.start = z ∧ p.finish ∈ B ∧ p.support ⊆ C.closureSet ∧ Preserves p :=
  C.target_paths z ⟨hzT, C.scheduled_mem⟩

/-! ## Completing the closure stage with outside-fragment geometry -/

/-- Boundary alignment is exactly the source endpoint-purity hypothesis of
the occurrence-aware fractured assignment theorem.  In particular, this is
not an ambient-source assertion: it only says that an uncovered fractured
initial cannot lie internally on the reference warp. -/
theorem uncoveredSourcesOutsideReference_of_initial_boundary
    {Zf : FracturedWarp Gamma}
    (h : Gamma.initialSet Zf.paths ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y) :
    FracturedDuplication.UncoveredSourcesOutsideReference Zf Y := by
  intro x hx
  intro hxY
  exact hx.2 (h ⟨hx.1, hxY⟩)

/-- The terminal half of boundary alignment is the corresponding truthful
terminal-contact purity condition for the duplicated-web theorem. -/
theorem terminalContactPure_of_terminal_boundary
    {Zf : FracturedWarp Gamma}
    (h : Gamma.terminalFrontier Zf.paths ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y) :
    FracturedDuplication.TerminalContactPure Zf Y :=
  h

/-- The fractured family obtained by restricting the auxiliary
`T_\alpha`--`T_\beta` linkage to the scheduled closure.

The closure construction itself does not choose this family.  Accordingly
the record contains precisely the outside-fragment conclusions used after
that choice: the four hypotheses of the fractured simultaneous-assignment
theorem and the five geometric facts which put every assigned alternating
path in the scope of Claim 2.  Keeping the five facts separate here makes
`AssignmentClosureContext` a constructed value rather than an opaque field
of the scheduled request. -/
structure ScheduledClosureFracturedOutsideFamily
    {z : V} {ZBefore innerRoof roof T B X0 : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves) where
  fractured : FracturedWarp Gamma
  source_side : Gamma.initialSet fractured.paths ⊆ Gamma.source
  target_side : Gamma.terminalFrontier fractured.paths ⊆ Gamma.target
  finite_character : Gamma.HasFiniteCharacter fractured.paths
  reference_initials : Gamma.initialSet Y ⊆
    Gamma.initialSet fractured.paths
  eligible_finite : ∀ (A : SimultaneousAssignment fractured.paths Y) s v,
    (A.assigned s).terminal? = some v →
      HammockEligible ZBefore innerRoof roof s.1 (.vertex v)
  eligible_infinite : ∀ (A : SimultaneousAssignment fractured.paths Y) s,
    (A.assigned s).IsInfinite →
      HammockEligible ZBefore innerRoof roof s.1 .infinity
  interior_disjoint_finite :
    ∀ (A : SimultaneousAssignment fractured.paths Y) s v,
      (h : (A.assigned s).terminal? = some v) →
        Disjoint
          (hammockInterior s.1 (.vertex v) (A.assigned s)) C.closureSet
  interior_disjoint_infinite :
    ∀ (A : SimultaneousAssignment fractured.paths Y) s,
      (A.assigned s).IsInfinite →
        Disjoint
          (hammockInterior s.1 .infinity (A.assigned s)) C.closureSet
  assigned_outside : ∀ (A : SimultaneousAssignment fractured.paths Y) s,
    ¬(A.assigned s).vertexSet ⊆ C.closureSet

/-- The outside-fragment facts are exactly an assignment closure context for
every simultaneous assignment of the fractured family. -/
theorem ScheduledClosureFracturedOutsideFamily.assignmentClosureContext
    {z : V} {ZBefore innerRoof roof T B X0 : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    {C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves}
    (F : ScheduledClosureFracturedOutsideFamily C)
    (A : SimultaneousAssignment F.fractured.paths Y) :
    AssignmentClosureContext A C.closureSet ZBefore innerRoof roof where
  eligible_finite := F.eligible_finite A
  eligible_infinite := F.eligible_infinite A
  interior_disjoint_finite := F.interior_disjoint_finite A
  interior_disjoint_infinite := F.interior_disjoint_infinite A
  outside := F.assigned_outside A

/-- Package already established outside-fragment facts in their structured
form.  This constructor is useful when the geometric restriction theorem
naturally proves `AssignmentClosureContext` as one conjunction. -/
def ScheduledClosureFracturedOutsideFamily.ofAssignmentClosureContexts
    {z : V} {ZBefore innerRoof roof T B X0 : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves)
    (fractured : FracturedWarp Gamma)
    (source_side : Gamma.initialSet fractured.paths ⊆ Gamma.source)
    (target_side : Gamma.terminalFrontier fractured.paths ⊆ Gamma.target)
    (finite_character : Gamma.HasFiniteCharacter fractured.paths)
    (reference_initials : Gamma.initialSet Y ⊆
      Gamma.initialSet fractured.paths)
    (closure_facts : ∀ A : SimultaneousAssignment fractured.paths Y,
      AssignmentClosureContext A C.closureSet ZBefore innerRoof roof) :
    ScheduledClosureFracturedOutsideFamily C where
  fractured := fractured
  source_side := source_side
  target_side := target_side
  finite_character := finite_character
  reference_initials := reference_initials
  eligible_finite := fun A ↦ (closure_facts A).eligible_finite
  eligible_infinite := fun A ↦ (closure_facts A).eligible_infinite
  interior_disjoint_finite :=
    fun A ↦ (closure_facts A).interior_disjoint_finite
  interior_disjoint_infinite :=
    fun A ↦ (closure_facts A).interior_disjoint_infinite
  assigned_outside := fun A ↦ (closure_facts A).outside

/-- The honest reference warp gives the unique unconditional instance of
`ScheduledClosureFracturedOutsideFamily` supported by the present ambient-web
interface.  Its assignment domain is empty, so the closure geometry is
vacuous.  This constructor is useful for separating the genuinely automatic
reference bookkeeping from the still non-vacuous intermediate-slice
fragmentation required by Assertion 9.31.

Notice that no claim is made that this family contains the scheduled vertex:
that would reintroduce the ambient-source error proved above. -/
def ScheduledClosureFracturedOutsideFamily.ofReferenceWarp
    {z : V} {ZBefore innerRoof roof T B X0 : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves)
    (hYwarp : Gamma.IsWarp Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hYfinite : Gamma.HasFiniteCharacter Y) :
    ScheduledClosureFracturedOutsideFamily C where
  fractured := honestFracturedWarp hYwarp
  source_side := by simpa using hYsource
  target_side := by simpa using hYtarget
  finite_character := by
    rw [honestFracturedWarp_paths]
    exact hYfinite
  reference_initials := by simp
  eligible_finite := by
    intro A s v hterminal
    exact False.elim (s.property.2 (by simpa using s.property.1))
  eligible_infinite := by
    intro A s hinfinite
    exact False.elim (s.property.2 (by simpa using s.property.1))
  interior_disjoint_finite := by
    intro A s v hterminal
    exact False.elim (s.property.2 (by simpa using s.property.1))
  interior_disjoint_infinite := by
    intro A s hinfinite
    exact False.elim (s.property.2 (by simpa using s.property.1))
  assigned_outside := by
    intro A s
    exact False.elim (s.property.2 (by simpa using s.property.1))

/-- A continuation-adapted closed request ties the scheduled endpoint to a
real path inside the closure.  It deliberately does not claim that the
endpoint is an initial vertex of the fractured outside family. -/
structure ContinuationAdaptedClosedFracturedReplacementRequest
    (z : V) (persistent B : Set V) where
  request : ClosedFracturedReplacementRequest
    (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent
  scheduled_target_path : ∃ p : FinitePath Gamma.graph,
    p.start = z ∧ p.finish ∈ B ∧ p.support ⊆ request.closureSet

/-- Continuation-indexed provider for the corrected scheduled request.  The
continuation supplies the slice endpoint; the returned request relates that
endpoint to its closed `z`--`B` path but leaves the assignment domain to the
outside-fragment construction. -/
def ContinuationAdaptedClosedFracturedReplacementRequestProvider
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (ContinuationAdaptedClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) z persistent B)

/-- The scheduled endpoint of a continuation-adapted request is genuinely
present in its closure set, without any ambient-source conclusion. -/
theorem ContinuationAdaptedClosedFracturedReplacementRequest.scheduled_mem_closureSet
    {z : V} {persistent B : Set V}
    (R : ContinuationAdaptedClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) z persistent B) :
    z ∈ R.request.closureSet := by
  obtain ⟨p, hpstart, _hpfinish, hpsupport⟩ := R.scheduled_target_path
  exact hpsupport (hpstart ▸ p.start_mem_support)

/-- The closure certificate becomes an ordinary closed fractured request
once the construction supplies the outside fractured family and the exact
assignment-closure facts.  These are precisely the geometric obligations
not provided by `exists_assertions_9_22_to_9_25`. -/
def ScheduledClosureRequest.toClosedFracturedReplacementRequest
    {z : V} {ZBefore innerRoof roof T B X0 persistent : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves)
    (fractured : FracturedWarp Gamma)
    (source_side : Gamma.initialSet fractured.paths ⊆ Gamma.source)
    (target_side : Gamma.terminalFrontier fractured.paths ⊆ Gamma.target)
    (finite_character : Gamma.HasFiniteCharacter fractured.paths)
    (reference_initials : Gamma.initialSet Y ⊆
      Gamma.initialSet fractured.paths)
    (closure_facts : ∀ A : SimultaneousAssignment fractured.paths Y,
      AssignmentClosureContext A C.closureSet ZBefore innerRoof roof) :
    ClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent where
  fractured := fractured
  closureSet := C.closureSet
  before := ZBefore
  innerRoof := innerRoof
  outerRoof := roof
  source_side := source_side
  target_side := target_side
  finite_character := finite_character
  reference_initials := reference_initials
  closed := C.hammock_closed
  closure_facts := closure_facts

/-- Completing the outside-fragment data also yields the corrected scheduled
request, with its `z`--`B` path obtained from Assertion 9.23. -/
def ScheduledClosureRequest.toContinuationAdaptedRequest
    {z : V} {ZBefore innerRoof roof T B X0 persistent : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves)
    (hzT : z ∈ T)
    (fractured : FracturedWarp Gamma)
    (source_side : Gamma.initialSet fractured.paths ⊆ Gamma.source)
    (target_side : Gamma.terminalFrontier fractured.paths ⊆ Gamma.target)
    (finite_character : Gamma.HasFiniteCharacter fractured.paths)
    (reference_initials : Gamma.initialSet Y ⊆
      Gamma.initialSet fractured.paths)
    (closure_facts : ∀ A : SimultaneousAssignment fractured.paths Y,
      AssignmentClosureContext A C.closureSet ZBefore innerRoof roof) :
    ContinuationAdaptedClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) z persistent B where
  request := C.toClosedFracturedReplacementRequest fractured source_side
    target_side finite_character reference_initials closure_facts
  scheduled_target_path := by
    obtain ⟨p, hpstart, hpfinish, hpsupport, _hpreserves⟩ :=
      C.exists_scheduled_target_path hzT
    exact ⟨p, hpstart, hpfinish, hpsupport⟩

/-- The structured outside family completes the scheduled closure to an
ordinary closed fractured replacement request. -/
def ScheduledClosureFracturedOutsideFamily.toClosedRequest
    {z : V} {ZBefore innerRoof roof T B X0 persistent : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    {C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves}
    (F : ScheduledClosureFracturedOutsideFamily C) :
    ClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent :=
  C.toClosedFracturedReplacementRequest F.fractured F.source_side
    F.target_side F.finite_character F.reference_initials
    F.assignmentClosureContext

/-- The structured outside family also completes the corrected scheduled
request.  Its distinguished path is the path supplied by the closure stage,
not an assertion that `z` is an ambient source. -/
def ScheduledClosureFracturedOutsideFamily.toContinuationAdaptedRequest
    {z : V} {ZBefore innerRoof roof T B X0 persistent : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    {C : ScheduledClosureRequest Gamma Y kappa z ZBefore innerRoof roof
      T B X0 Preserves}
    (F : ScheduledClosureFracturedOutsideFamily C)
    (hzT : z ∈ T) :
    ContinuationAdaptedClosedFracturedReplacementRequest
      (Gamma := Gamma) (Y := Y) (kappa := kappa) z persistent B :=
  C.toContinuationAdaptedRequest hzT F.fractured F.source_side F.target_side
    F.finite_character F.reference_initials F.assignmentClosureContext

end LinkageBlueprint
end Blueprint
end Erdos599
