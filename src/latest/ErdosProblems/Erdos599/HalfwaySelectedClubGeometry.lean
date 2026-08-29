/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLadderReference
import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport
import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.SliceRestrictedDelta

/-!
# Selecting the club before installing its reference warp

The reference warp used by the half-way transaction is indexed by the
selected later ladder stage.  It therefore cannot be an input to the
transfinite club-selection recursion: that stage does not exist yet.

This file records the strongest unconditional construction at this point of
the argument.  The closed-stage family is the constant designated source set
`A0`; its monotonicity, cardinal bound, containment in every ladder roof, and
its strict-initial-union equation are all derived.  After the club has chosen
the later stage, `ClubStageGeometry.withReference` installs the actual
stage-dependent `ladderReference`.  Its warp, finite-character, frontier, and
roof-containment facts are consequences of legality.

Hammock containment and paths from the old frontier to the new frontier are
deliberately not fields of this club-selection theorem.  They belong to the
subsequent one-stage Section 9 transaction.  In particular, a fixed reference
cannot be required to lie below every earlier ladder frontier and then be
replaced by a family which is only defined after the later stage is selected.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-! ## Installing the closure after the club stage is selected -/

/-- Replace the dummy club-selection family by the actual closure `X` at
and after the selected transaction stage.  Before that stage the family is
the designated seed `A0`.

This is the dependency-correct way to combine club selection with the omega
closure: the club and its later stage are selected first; Assertions
9.22--9.25 then construct `X`; only afterwards is `X` installed as
`closedSet`.  Monotonicity uses exactly `A0 ⊆ X`. -/
def withTransactionClosure
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    ClubStageGeometry Gamma Y kappa theta where
  ladder := C.ladder
  legal := C.legal
  hindranceRungs := C.hindranceRungs
  hindranceObstruction := C.hindranceObstruction
  normalized := C.normalized
  club := C.club
  club_isClub := C.club_isClub
  club_avoids_phi := C.club_avoids_phi
  oldStage := C.oldStage
  newStage := C.newStage
  old_mem_club := C.old_mem_club
  new_mem_club := C.new_mem_club
  old_lt_new := C.old_lt_new
  closedStage := fun a => if C.newStage ≤ a then X else A0
  closedStage_mono := by
    intro a b hab
    by_cases hna : C.newStage ≤ a
    · have hnb : C.newStage ≤ b := hna.trans hab
      simpa only [if_pos hna, if_pos hnb] using
        (Set.Subset.rfl : X ⊆ X)
    · by_cases hnb : C.newStage ≤ b
      · simpa only [if_neg hna, if_pos hnb] using hA0X
      · simpa only [if_neg hna, if_neg hnb] using
          (Set.Subset.rfl : A0 ⊆ A0)
  before_card := by
    apply (Cardinal.mk_subtype_mono ?_).trans hXcard
    rintro x ⟨a, ha, hxa⟩
    have hnot : ¬ C.newStage ≤ a := not_le_of_gt ha
    exact hA0X (by simpa only [if_neg hnot] using hxa)
  capacity_infinite := C.capacity_infinite

@[simp] theorem withTransactionClosure_ladder
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).ladder = C.ladder := rfl

@[simp] theorem withTransactionClosure_oldStage
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).oldStage = C.oldStage := rfl

@[simp] theorem withTransactionClosure_newStage
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).newStage = C.newStage := rfl

@[simp] theorem withTransactionClosure_closedSet
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).closedSet = X := by
  simp only [ClubStageGeometry.closedSet, withTransactionClosure, if_pos le_rfl]

@[simp] theorem withTransactionClosure_before
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).before = A0 := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, ha, hxa⟩
    have hnot : ¬ C.newStage ≤ a := not_le_of_gt ha
    simpa only [withTransactionClosure_newStage,
      withTransactionClosure, if_neg hnot] using hxa
  · intro x hx
    refine ⟨C.oldStage, ?_, ?_⟩
    · simpa only [withTransactionClosure_newStage] using C.old_lt_new
    · have hnot : ¬ C.newStage ≤ C.oldStage := not_le_of_gt C.old_lt_new
      simpa only [withTransactionClosure, if_neg hnot] using hx

@[simp] theorem withTransactionClosure_selectedReference
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).selectedReference =
      C.selectedReference := rfl

@[simp] theorem withTransactionClosure_oldSlice
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).oldSlice =
      C.oldSlice := rfl

@[simp] theorem withTransactionClosure_newSlice
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).newSlice =
      C.newSlice := rfl

@[simp] theorem withTransactionClosure_innerRoof
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).innerRoof =
      C.innerRoof := rfl

@[simp] theorem withTransactionClosure_outerRoof
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).outerRoof =
      C.outerRoof := rfl

@[simp] theorem withTransactionClosure_persistent
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A0 X : Set V) (hA0X : A0 ⊆ X) (hXcard : #X ≤ kappa) :
    (C.withTransactionClosure A0 X hA0X hXcard).persistent =
      C.persistent := rfl

/-- Two chronologically ordered legal ladder frontiers have the exact
finite-path relation used by Assertion 9.23.  Essentiality of the old
frontier gives a target path from `v`; roofing by the new frontier makes
that path meet the new frontier; taking its first hit keeps the entire
prefix below the new roof. -/
theorem exists_path_to_later_frontier
    {L : Gamma.KappaLadder kappa}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a b : Ladder.Stage kappa} (hab : a < b) {v : V}
    (hv : v ∈ L.frontier a) :
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ L.frontier b ∧
        p.support ⊆ Gamma.roof (L.frontier b) := by
  have hvEssential : v ∈ Gamma.essential (L.frontier a) := by
    rw [hL.frontiersEssential a]
    exact hv
  obtain ⟨p, hpTarget, _hpAvoid⟩ :=
    (Gamma.not_mem_roof_iff ((L.frontier a) \ {v}) v).1
      hvEssential.2
  have hvRoof : v ∈ Gamma.roof (L.frontier b) :=
    hL.frontierChronology hab hv
  have hpStartRoof : p.start ∈ Gamma.roof (L.frontier b) := by
    rw [hpTarget.1]
    exact hvRoof
  have hmeet : p.walk.Meets (L.frontier b) :=
    hvRoof p hpTarget
  let q := p.firstHit (L.frontier b) hmeet
  refine ⟨q, ?_, p.firstHit_finish_mem (L.frontier b) hmeet, ?_⟩
  · change p.start = v
    exact hpTarget.1
  · exact CardinalInduction.SliceRestrictedDelta.firstHit_support_subset_roof_ambient
      Gamma (L.frontier b) p hpStartRoof hmeet

/-- Selected-stage specialization of `exists_path_to_later_frontier`.
This discharges the `target_paths` field of a club-stage seed with the
predicate `Preserves := fun _ => True`. -/
theorem oldSlice_target_paths
    {Y : Set Gamma.DPath} {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta) :
    ∀ v ∈ C.oldSlice ∩ C.outerRoof,
      ∃ p : FinitePath Gamma.graph,
        p.start = v ∧ p.finish ∈ C.newSlice ∧
          p.support ⊆ C.outerRoof ∧ True := by
  intro v hv
  obtain ⟨p, hpStart, hpFinish, hpRoof⟩ :=
    exists_path_to_later_frontier C.legal C.old_lt_new hv.1
  exact ⟨p, hpStart, hpFinish, hpRoof, trivial⟩

/-- Select the canonical club with the concrete constant source seed, and
then expose all facts about the genuine later-stage reference.

The base geometry is indexed by the empty dummy reference because
`ClubStageGeometry` itself contains no reference-dependent field.  Consumers
should use
`C0.withReference C0.selectedReference` for the one-stage transaction. -/
theorem exists_selectedReference_of_designatedSource
    (hkappa : aleph0 <= kappa)
    (hGamma : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (preferred : Ladder.Stage (succ kappa) -> Option V)
    (A0 : Set V) (hA0source : A0 ⊆ Gamma.source)
    (hA0card : #A0 = kappa)
    (hground :
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma (succ kappa) preferred
      DWeb.KappaLadder.Deferred.IsKappaHindrance L ->
        exists W : Set Gamma.DPath, Gamma.IsHindrance W) :
    ∃ C0 : ClubStageGeometry Gamma (∅ : Set Gamma.DPath)
        kappa (succ kappa),
      C0.closedStage = (fun _ => A0) ∧
      C0.closedSet = A0 ∧
      C0.before = A0 ∧
      (∀ a, C0.closedStage a ⊆ Gamma.roof (C0.ladder.frontier a)) ∧
      (let C := C0.withReference C0.selectedReference
       Gamma.IsWarp C0.selectedReference ∧
        Gamma.HasFiniteCharacter C0.selectedReference ∧
        Gamma.terminalFrontier C0.selectedReference = C.newSlice ∧
        (∀ p ∈ C0.selectedReference, p.support ⊆ C.outerRoof)) := by
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    Gamma (succ kappa) preferred
  have hsuccRegular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have hsuccUncountable : aleph0 < succ kappa :=
    hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hL : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      preferred hsuccRegular hsuccUncountable hNoEnter
  have hRungs : ∀ a, ¬ (L.stageWeb a).IsUnhindered →
      (L.stageWeb a).IsHindrance (L.rung a) := by
    intro a hstage
    exact DWeb.KappaLadder.canonicalLadderCore_rung_isHindrance
      (G := Gamma) (succ kappa) preferred a hstage
  have hindranceObstruction : L.phiHindrance ⊆
      DWeb.KappaLadder.Deferred.phi L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_phiHindrance_subset_phi
      preferred hsuccRegular hsuccUncountable hGamma hNoEnter
  have hnonstationary :
      ¬ Stationary.IsStationaryBelow (succ kappa)
        (DWeb.KappaLadder.Deferred.phi L) := by
    intro hstationary
    obtain ⟨W, hW⟩ := hground ⟨hL, hstationary⟩
    exact hUnhindered ⟨W, hW⟩
  obtain ⟨Sigma, hSigma, hdisjoint⟩ :=
    not_isStationary_iff.mp hnonstationary
  have havoid : Disjoint Sigma
      (DWeb.KappaLadder.Deferred.phi L) := hdisjoint.symm
  let zero : Ladder.Stage (succ kappa) := ⟨0, hL.regular.ord_pos⟩
  let oldStage := RegularCardinal.nextInClub hL.regular Sigma hSigma zero
  let newStage := RegularCardinal.nextInClub hL.regular Sigma hSigma oldStage
  let C0 : ClubStageGeometry Gamma (∅ : Set Gamma.DPath)
      kappa (succ kappa) := {
    ladder := L
    legal := hL
    hindranceRungs := hRungs
    hindranceObstruction := hindranceObstruction
    normalized := hGamma
    club := Sigma
    club_isClub := hSigma
    club_avoids_phi := havoid
    oldStage := oldStage
    newStage := newStage
    old_mem_club := RegularCardinal.nextInClub_mem
      hL.regular Sigma hSigma zero
    new_mem_club := RegularCardinal.nextInClub_mem
      hL.regular Sigma hSigma oldStage
    old_lt_new := RegularCardinal.lt_nextInClub
      hL.regular Sigma hSigma oldStage
    closedStage := fun _ => A0
    closedStage_mono := by
      intro _a _b _hab
      exact Set.Subset.rfl
    before_card := by
      apply (Cardinal.mk_subtype_mono ?_).trans hA0card.le
      rintro x ⟨_a, _ha, hxa⟩
      exact hxa
    capacity_infinite := hkappa }
  have hclosed : C0.closedStage = (fun _ => A0) := rfl
  have hclosedSet : C0.closedSet = A0 := rfl
  have hbefore : C0.before = A0 := by
    apply Set.Subset.antisymm
    · rintro x ⟨_a, _ha, hxa⟩
      exact hxa
    · intro x hx
      exact ⟨C0.oldStage, C0.old_lt_new, hx⟩
  have hclosedRoof : ∀ a,
      C0.closedStage a ⊆ Gamma.roof (C0.ladder.frontier a) := by
    intro a x hx
    apply hA0source at hx
    rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a,
      Gamma.roof_essential]
    exact hL.roofsSourceAtStages (Ladder.Stage.toExtended a) hx
  have hrefRoof : ∀ p ∈ C0.selectedReference,
      p.support ⊆ Gamma.roof (C0.ladder.frontier C0.newStage) := by
    intro p hp x hxp
    apply ladderReference.vertexSet_subset_roof C0.legal
      (DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
        C0.legal C0.newStage)
    exact ⟨p, hp, hxp⟩
  refine ⟨C0, hclosed, hclosedSet, hbefore, hclosedRoof, ?_⟩
  dsimp only
  refine ⟨C0.selectedReference_isWarp,
    C0.selectedReference_finiteCharacter, ?_, ?_⟩
  · change Gamma.terminalFrontier C0.selectedReference = C0.newSlice
    exact C0.terminalFrontier_selectedReference
  · change ∀ p ∈ C0.selectedReference,
      p.support ⊆ Gamma.roof (C0.ladder.frontier C0.newStage)
    exact hrefRoof

end ClubStageGeometry
end LinkageBlueprint
end Blueprint
end Erdos599
