/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSourceFirst
import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantEndpointOpen
import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantRootNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedReducedDeletedOutcome
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorOutput

/-!
# Source-first normalization at the relevant split grounding frontier

Membership in the source-first relevant frontier supplies the endpoint-open
ambient prefix needed to normalize the two escaping-fragment constructors.
An ordinary escape forces the boundary endpoint itself to be an ambient
source.  If that source is not the deliberately omitted reserved source,
reflexive reachability contradicts the root failure.  Thus the only source
endpoint left is the reserved source itself; every other escaping leaf keeps
an actual virtual forward step.  Deleted incoming edges are simultaneously
refined to the concrete backward/last-contact/boundary-departure trichotomy.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev SourceFirstNormalizationInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev SourceFirstNormalizationIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev SourceFirstNormalizationEdges (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (SourceFirstNormalizationIndexed (L := L) (hL := hL)
      (hground := hground)) S K T

/-- Exact residual alternatives at an unrooted source-first relevant point.

The old ordinary-start escape alternatives are absent.  The `sourceEndpoint`
constructor is forced to be the one source intentionally removed from the
allowed root set.  The `virtualEscape` constructor retains both the
reserved/hanging origin and its genuine virtual first step. -/
inductive SplitGroundedRelevantSourceFirstFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) (t : V) : Prop
  | finite
      (ht : t ∈ (SourceFirstNormalizationInput
        (L := L) (hL := hL)).finiteSource)
      (data : SplitGroundedUnusedRecord.SplitGroundedReducedFiniteSourceRootFailureAt
        R T t ht)
  | sourceEndpoint
      (endpoint_eq : t = R.record.initial)
  | virtualEscape
      (P : (SourceFirstNormalizationInput
        (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut P = t)
      (origin :
        (P.parent = R.record ∧ P.path.initial = P.parent.initial) ∨
        (P.IsHanging ∧ P.path.initial = P.parent.initial))
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
      (escape : SplitGroundedRelevantVirtualEscape L hL.legal S.cut t)
  | deleted
      (P : (SourceFirstNormalizationInput
        (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut P = t)
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (segment_finish : segment.finish = GroundingCut.blockingPoint
        (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut P)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (SourceFirstNormalizationEdges (L := L) (hL := hL)
          (hground := hground) (S := S) (K := K) T))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a lastDeleted.head)
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T P.parent segment lastDeleted)

namespace SplitGroundedUnusedRecord

private theorem sourceFirst_endpoint_eq_reserved_of_not_rooted
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {t : V}
    (htSource : t ∈ Gamma.source)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t) :
    t = R.record.initial := by
  by_contra hne
  apply hnot
  exact ⟨t, ⟨htSource, by simpa only [Set.mem_singleton_iff]⟩,
    Relation.ReflTransGen.refl⟩

/-- Normalize one unrooted point of the source-first relevant frontier.
This is where endpoint-open finite descent is actually consumed. -/
theorem relevantSourceFirstBBRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {t : V}
    (hC : Popular.IsSeparator
      (SourceFirstNormalizationInput (L := L) (hL := hL)).lambda S.cut)
    (ht : t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t)
    (hcontrol : ∀ c : ControlRequest
        (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    SplitGroundedRelevantSourceFirstFailureAt R T t := by
  obtain ⟨Q, hQsource, hQfinish, hQroof, hQboundary, hQfirst⟩ := ht
  have hold := R.relevantBBRootFailureAt T hQboundary hnot hcontrol
  cases hold with
  | finite hfinite data =>
      exact .finite hfinite data
  | blocking P hP point_eq data =>
      cases data with
      | reservedEscape parent_eq initial_eq meets_escape initial_not_rooted =>
          have hblock : GroundingCut.blockingPoint
              (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut P =
              Q.finish := point_eq.trans hQfinish.symm
          rcases L.splitGroundedRelevant_sourceFirst_escapeBlocker_source_or_virtual
              hL.legal S.cut hC Q hQsource hQroof
                (hfirst := fun {_} hx ↦ hQfirst _ hx)
                P hP hblock meets_escape with hsource | hvirtual
          · exact .sourceEndpoint
              (R.sourceFirst_endpoint_eq_reserved_of_not_rooted T
                (hQfinish ▸ hsource) hnot)
          · exact .virtualEscape P hP point_eq
              (Or.inl ⟨parent_eq, initial_eq⟩) initial_not_rooted
                (hQfinish ▸ hvirtual.some)
      | hangingEscape parent_hanging initial_eq meets_escape initial_not_rooted =>
          have hblock : GroundingCut.blockingPoint
              (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut P =
              Q.finish := point_eq.trans hQfinish.symm
          rcases L.splitGroundedRelevant_sourceFirst_escapeBlocker_source_or_virtual
              hL.legal S.cut hC Q hQsource hQroof
                (hfirst := fun {_} hx ↦ hQfirst _ hx)
                P hP hblock meets_escape with hsource | hvirtual
          · exact .sourceEndpoint
              (R.sourceFirst_endpoint_eq_reserved_of_not_rooted T
                (hQfinish ▸ hsource) hnot)
          · exact .virtualEscape P hP point_eq
              (Or.inr ⟨parent_hanging, initial_eq⟩) initial_not_rooted
                (hQfinish ▸ hvirtual.some)
      | deleted segment segment_start segment_finish segment_support
          segment_edges lastDeleted head_not_rooted deleted_class =>
          exact .deleted P hP point_eq segment segment_start segment_finish
            segment_support segment_edges lastDeleted head_not_rooted
              (L.splitGroundedReducedDeletedOutcomeAt T P.parent segment
                P.parent_mem (segment_support.trans P.support_subset)
                  (segment_edges.trans P.edges_subset) lastDeleted
                    deleted_class)

/-- Pointwise totalization over the actual source-first separator. -/
theorem relevantSourceFirstFrontier_rootedAt_or_failure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hC : Popular.IsSeparator
      (SourceFirstNormalizationInput (L := L) (hL := hL)).lambda S.cut)
    (hcontrol : ∀ c : ControlRequest
        (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
          a c.1) :
    (∀ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
          a t) ∨
      ∃ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
        SplitGroundedRelevantSourceFirstFailureAt R
          (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut) t := by
  classical
  by_cases hall : ∀ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
          a t
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨t, ht, hnot⟩ := hall
    have hnot' : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
          a t := by
      rintro ⟨a, ha, hareach⟩
      exact hnot a ha hareach
    exact ⟨t, ht,
      R.relevantSourceFirstBBRootFailureAt
        (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
          hC ht hnot' hcontrol⟩

end SplitGroundedUnusedRecord

/-- Assertion 8.22 succeeds on the source-first relevant separator, or
one of the four exact residual alternatives above remains. -/
theorem exists_hindrance_or_splitGroundedRelevantSourceFirstFailure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hC : Popular.IsSeparator
      (SourceFirstNormalizationInput (L := L) (hL := hL)).lambda S.cut)
    (hcontrol : ∀ c : ControlRequest
        (SourceFirstNormalizationInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
          a c.1) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
        SplitGroundedRelevantSourceFirstFailureAt R
          (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut) t := by
  let T := L.splitGroundedRelevantSourceFirstBB hL.legal S.cut
  rcases R.relevantSourceFirstFrontier_rootedAt_or_failure hC hcontrol with
      hroot | hfailure
  · left
    have houtput :=
      L.splitGroundedAssertion822Output_of_frontierGeometry_withControls
        R T
          ((L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut).trans
            (L.splitGroundedRelevantBB_subset_legacyBB hL.legal S.cut))
          (L.splitGroundedRelevantSourceFirstBB_isSeparator hL.legal S.cut hC)
          hroot
    exact exists_hindrance_of_splitGroundedAssertion822Output houtput.some
  · exact Or.inr hfailure

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.relevantSourceFirstBBRootFailureAt
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_or_splitGroundedRelevantSourceFirstFailure
