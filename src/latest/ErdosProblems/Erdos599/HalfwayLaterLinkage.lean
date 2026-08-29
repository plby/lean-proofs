/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySelectedClubGeometry
import ErdosProblems.Erdos599.HalfwayCurrentTargetRow
import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.SliceFirstHitSegment

/-!
# Selecting the later linkage before the omega closure

The current-cardinal extension clause gives a linkage from the designated
`kappa`-set of sources to the ambient target.  At a selected ladder stage,
every designated source lies in the roof of the selected frontier.  We may
therefore stop each member of that linkage at its first visit to the
frontier.  The resulting family is selected before the closing operation,
is a finite-character linkage to the selected frontier, and lies wholly in
its roof.

The last field below records more than support containment: every stopped
member is an ordinary path fragment of one member of the ambient target
linkage.  This is the precise `P`-containment fact used by later cut and
replacement constructions.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder
open CardinalInduction
open CardinalInduction.ControlledSlices
open CardinalInduction.SliceCandidate

universe u

variable {V : Type u}
variable {Gamma : DWeb V}
variable {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- A set lying in the roof of `T` is separated from the ambient target by
`T`.  This is the direct specialization of nested-roof separation: the
ambient target is trimmed and roofs every vertex. -/
theorem separates_target_of_subset_roof
    {A T : Set V} (hAT : A ⊆ Gamma.roof T) :
    RelationalRoof.Separates Gamma.graph.Adj A Gamma.target T := by
  apply RelationalRoof.nested_roofs_separate
      (R := Gamma.graph.Adj) (B := Gamma.target)
  · exact (target_subset_isTrimmedSeparator
      (Γ := Gamma) (C := Gamma.target) Set.Subset.rfl).symm
  · exact Gamma.roof_cut hAT
  · change Gamma.roof T ⊆ Gamma.roof Gamma.target
    rw [roof_target]
    exact Set.subset_univ _

/-- All data supplied by selecting the current-cardinal target linkage and
stopping it at the selected later frontier. -/
structure CurrentLaterLinkage
    (C : ClubStageGeometry Gamma Y kappa theta) (A0 : Set V) where
  /-- The linkage to the ambient target supplied by the extension clause. -/
  ambient : Set Gamma.DPath
  /-- Its componentwise first-hit truncation at the selected frontier. -/
  later : Set Gamma.DPath
  ambient_linkage : IsLinkageBetween Gamma A0 Gamma.target ambient
  later_linkage : IsLinkageBetween Gamma A0 C.newSlice later
  later_in_outerRoof : ∀ p ∈ later, p.support ⊆ C.outerRoof
  later_is_ambient_fragment : ∀ p ∈ later,
    IsLadderFragment Gamma ambient p

namespace CurrentLaterLinkage

variable {C : ClubStageGeometry Gamma Y kappa theta} {A0 : Set V}

theorem later_isWarp (D : CurrentLaterLinkage C A0) :
    Gamma.IsWarp D.later :=
  D.later_linkage.isWarp

theorem later_finite (D : CurrentLaterLinkage C A0) :
    Gamma.HasFiniteCharacter D.later :=
  D.later_linkage.finiteCharacter

@[simp] theorem initialSet_later (D : CurrentLaterLinkage C A0) :
    Gamma.initialSet D.later = A0 :=
  D.later_linkage.initialSet_eq

theorem terminalFrontier_later_subset
    (D : CurrentLaterLinkage C A0) :
    Gamma.terminalFrontier D.later ⊆ C.newSlice :=
  D.later_linkage.terminalFrontier_subset

/-- Support-only projection of the stronger ambient-fragment field. -/
theorem exists_ambient_support
    (D : CurrentLaterLinkage C A0) {q : Gamma.DPath} (hq : q ∈ D.later) :
    ∃ p ∈ D.ambient, q.support ⊆ p.support := by
  obtain ⟨p, hp, hqp⟩ := D.later_is_ambient_fragment q hq
  exact ⟨p, hp, hqp.1⟩

end CurrentLaterLinkage

/-- The selected ladder frontier roofs the entire ambient source. -/
theorem ClubStageGeometry.source_subset_outerRoof
    (C : ClubStageGeometry Gamma Y kappa theta) :
    Gamma.source ⊆ C.outerRoof := by
  intro x hx
  change x ∈ Gamma.roof (C.ladder.frontier C.newStage)
  rw [C.ladder.frontier_eq_essential_terminalFrontier
      C.legal.roofsSourceAtStages C.newStage,
    Gamma.roof_essential]
  exact C.legal.roofsSourceAtStages
    (Ladder.Stage.toExtended C.newStage) hx

/-- Unconditional construction of the later linkage used by the
linkage-first closure.

The only choice is the current-cardinal target linkage `P`.  Once `P` is
chosen, `later` is its canonical first-hit prefix family at `C.newSlice`.
In particular this construction does not mention the subsequent omega
closure set. -/
theorem ClubStageGeometry.exists_currentLaterLinkage
    (C : ClubStageGeometry Gamma Y kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsUnhindered)
    {A0 : Set V} (hA0source : A0 ⊆ Gamma.source)
    (hA0card : #A0 = kappa) :
    Nonempty (CurrentLaterLinkage C A0) := by
  obtain ⟨P, hP⟩ :=
    exists_designatedSourceLinkage_of_current
      hext Gamma hGamma C.normalized hA0source hA0card
  have hA0roof : A0 ⊆ C.outerRoof :=
    hA0source.trans C.source_subset_outerRoof
  let hsep : RelationalRoof.Separates Gamma.graph.Adj
      A0 Gamma.target C.newSlice :=
    separates_target_of_subset_roof hA0roof
  let W : Set Gamma.DPath := firstHitPrefixFamily hP hsep
  have hW : IsLinkageBetween Gamma A0 C.newSlice W :=
    firstHitPrefixFamily_isLinkageBetween hP hsep
  have hWroof : ∀ q ∈ W, q.support ⊆ C.outerRoof := by
    rintro q hq
    change q ∈ SliceSegmentCore.segmentFamily
      (firstHitSegmentRealization hP hsep) at hq
    obtain ⟨a, rfl⟩ := hq
    change (linkageFirstHitAt hP hsep a).support ⊆ C.outerRoof
    exact SliceRestrictedDelta.firstHit_support_subset_roof_ambient
      Gamma C.newSlice (linkageFiniteAt hP a)
      (by simpa only [linkageFiniteAt_start] using hA0roof a.2)
      (linkageFiniteAt_meets hP hsep a)
  have hWfragment : ∀ q ∈ W, IsLadderFragment Gamma P q := by
    change ∀ q ∈ SliceSegmentCore.segmentFamily
        (firstHitSegmentRealization hP hsep),
      IsLadderFragment Gamma P q
    exact SliceSegmentCore.segmentFamily_isLadderFragment
      (firstHitSegmentRealization hP hsep)
  exact ⟨{
    ambient := P
    later := W
    ambient_linkage := hP
    later_linkage := hW
    later_in_outerRoof := hWroof
    later_is_ambient_fragment := hWfragment }⟩

end LinkageBlueprint
end Blueprint
end Erdos599
