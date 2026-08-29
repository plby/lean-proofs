/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLinkageFirstClosure
import ErdosProblems.Erdos599.HalfwayOutsideReferenceInsideSplice

/-!
# The concrete linkage-first outside-reference request

The later row is selected before the omega closure.  The closure is then
performed under both the full reference and that later row.  If the later
row contains the reference, its literal outside cut has the exact boundary
needed for Theorem 4.12 relative to `outsideReference Y X`; no cut-dependent
boundary oracle is needed.

This file packages the resulting actual closed set, literal split fracture,
pruned boundary, and full-reference Claim 2 assignment.  It supersedes the
older linkage-first adapter whose output required the false full-reference
`reference_initials` boundary field.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Source-level data for the repaired order.  The endpoint compatibility
of the two rows is not assumed separately: it follows from `Y ⊆ later` and
the warp property of `later`. -/
structure LinkageFirstOutsideReferenceSeed extends
    LinkageFirstClosureSeed (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  reference_subset_later : Y ⊆ later
  source_location :
    Gamma.initialSet later \ Gamma.initialSet Y ⊆ before ∩ innerRoof
  terminal_location :
    Gamma.terminalFrontier later \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof

/-- The literal output of the linkage-first closing operation.  All fields
are data or conclusions of the omega-closure theorem; in particular there
is no arbitrary-cut assignment or boundary hypothesis. -/
structure LinkageFirstOutsideReferenceRequest
    (S : LinkageFirstOutsideReferenceSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) where
  closureSet : Set V
  initialSeed_subset : S.initialSeed ⊆ closureSet
  closure_card : #closureSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma Y closureSet
    S.before S.innerRoof S.outerRoof kappa
  large_closed : LargeHammockClosed Gamma Y closureSet
    S.before S.innerRoof S.outerRoof kappa
  preserving_target_paths : HasPreservingTargetPaths Gamma S.targetSlice
    closureSet S.targetSide S.Preserves
  reference_closed : ClosedUnderPaths Gamma Y closureSet
  later_closed : ClosedUnderPaths Gamma S.later closureSet
  contained_in_roof : ContainedInRoof closureSet S.outerRoof
  split : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
    S.later closureSet
  boundary : OutsideCutBoundary
    (Y := outsideReference Y closureSet) S.later closureSet
      S.before S.innerRoof S.outerRoof
  assignment : OutsideReferenceClaim2Assignment
    (Y := Y) (before := S.before) (innerRoof := S.innerRoof)
    (outerRoof := S.outerRoof) split.outside

namespace LinkageFirstOutsideReferenceSeed

/-- Run Assertions 9.22--9.25 after selecting the later row, construct the
literal occurrence-split outside family, and perform the repaired Theorem
4.12/Claim 2 handoff. -/
theorem exists_request
    (S : LinkageFirstOutsideReferenceSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) :
    Nonempty (LinkageFirstOutsideReferenceRequest S) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, htarget,
      hreference, hlater, hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_rowClosure Gamma Y S.later
      kappa kappa S.before S.innerRoof S.outerRoof S.targetSlice
      S.targetSide S.initialSeed S.Preserves S.target_paths
      S.reference_isWarp S.later_isWarp S.reference_in_roof
      S.later_in_roof S.safe_in_roof S.kappa_infinite (le_refl kappa)
      S.before_card S.initial_card S.initial_in_roof
  let F := (exists_splitProjectedOutsideFracturedWarp S.later X
    S.later_isWarp S.later_finite).some
  let B : OutsideCutBoundary (Y := outsideReference Y X)
      S.later X S.before S.innerRoof S.outerRoof :=
    OutsideCutBoundary.of_closedUnderLater_outsideReference_of_subset
      S.later_isWarp hlater S.reference_isWarp hreference
      S.reference_subset_later S.source_location S.terminal_location
  let A := (F.exists_outsideReferenceClaim2Assignment
    hlater hreference S.reference_isWarp S.reference_finite B).some
  exact ⟨{
    closureSet := X
    initialSeed_subset := hseed
    closure_card := hcard
    hammock_closed := hclosed
    large_closed := hlarge
    preserving_target_paths := htarget
    reference_closed := hreference
    later_closed := hlater
    contained_in_roof := hroof
    split := F
    boundary := B
    assignment := A }⟩

end LinkageFirstOutsideReferenceSeed

namespace LinkageFirstOutsideReferenceRequest

variable {S : LinkageFirstOutsideReferenceSeed
  (Gamma := Gamma) (Y := Y) (kappa := kappa)}

/-- The finite assigned endpoints and infinite sources of the actual request
are immediately classified by the original full-reference Claim 2. -/
theorem classified
    {persistent : Set V}
    (R : LinkageFirstOutsideReferenceRequest S) :
    (∀ s v,
        (R.assignment.bracket.assignment.assigned s).terminal? = some v →
          IsImaginaryEdge Gamma Y kappa s.1 v) ∧
      (∀ s, (R.assignment.bracket.assignment.assigned s).IsInfinite →
          IsPopular Gamma Y persistent kappa s.1) :=
  R.assignment.classified R.hammock_closed

end LinkageFirstOutsideReferenceRequest

end LinkageBlueprint
end Blueprint
end Erdos599

