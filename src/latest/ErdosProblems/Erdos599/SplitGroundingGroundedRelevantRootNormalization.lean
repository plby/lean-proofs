/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantBoundaryOwner
import ErdosProblems.Erdos599.SplitGroundingGroundedReducedRootNormalization
import ErdosProblems.Erdos599.SplitGroundingEqualHangingStage

/-!
# Root normalization for the descent-relevant boundary

The reduced root normal form still contains a finite escape-free leaf for
an arbitrary inessential hanging component.  Such a component is absent
from `splitGroundedRelevantG0`.  Refining the old normal form with relevant
membership removes the reserved-terminal leaf entirely and strengthens the
only remaining escape-free hanging leaf to an essential component ending in
the global essential terminal cut.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev RelevantRootInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev RelevantRootIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev RelevantRootEdges (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (RelevantRootIndexed (L := L) (hL := hL) (hground := hground)) S K T

/-- The initial vertex of an essential hanging limiting component is one
of the grounded auxiliary's target markers. -/
theorem splitGrounded_hangingEssential_initial_mem_targetMarkers
    (P : (RelevantRootInput (L := L) (hL := hL)).Fragment)
    (hessential : P.parent ∈
      (RelevantRootInput (L := L) (hL := hL)).essentialLadder)
    (hhanging : P.IsHanging) :
    P.parent.initial ∈
      (RelevantRootInput (L := L) (hL := hL)).targetMarkers := by
  obtain ⟨a, ha⟩ :=
    hL.legal.exists_splitMarkerStage_of_mem_limitWarp_of_hanging
      hessential.1 hhanging
  exact ⟨⟨a, ha⟩, ⟨P.parent, hessential,
    P.parent.initial_mem_support⟩⟩

/-- If the first fragment of an essential hanging component is
escape-free, its marker initial must already be represented in `C_V`.
Otherwise the trivial Lambda path at that target marker is an ordinary
escape from the fragment initial. -/
theorem splitGrounded_hangingEssentialFirst_notEscape_initial_mem_CV
    (P : (RelevantRootInput (L := L) (hL := hL)).Fragment)
    (hessential : P.parent ∈
      (RelevantRootInput (L := L) (hL := hL)).essentialLadder)
    (hhanging : P.IsHanging)
    (hfirst : P.path.initial = P.parent.initial)
    (hnoEscape : ¬ P.MeetsEscape
      (RelevantRootInput (L := L) (hL := hL)) S.cut) :
    P.path.initial ∈ GroundingCut.CV
      (RelevantRootInput (L := L) (hL := hL)) S.cut := by
  rw [GroundingCut.mem_CV]
  by_contra hnotC
  let y := P.parent.initial
  have hyNotC :
      (PopularAuxiliary.Input.LambdaVertex.old y :
        (RelevantRootInput (L := L) (hL := hL)).LV) ∉ S.cut := by
    simpa only [y, ← hfirst] using hnotC
  let q : FinitePath
      (RelevantRootInput (L := L) (hL := hL)).lambda.graph :=
    FinitePath.trivial
      (RelevantRootInput (L := L) (hL := hL)).lambda.graph (.old y)
  let E : GroundingRelaxedEscape.RelaxedEscape
      (RelevantRootInput (L := L) (hL := hL)) S.cut y :=
    { route := q
      start_eq := Or.inl (by simp [q])
      target := by
        simpa [q] using
          ((RelevantRootInput (L := L) (hL := hL)).mem_lambda_target_old y).2
            (splitGrounded_hangingEssential_initial_mem_targetMarkers
              P hessential hhanging)
      avoids := by
        change Disjoint q.support S.cut
        rw [Set.disjoint_left]
        intro z hz hzC
        have hzEq : z =
            (PopularAuxiliary.Input.LambdaVertex.old y :
              (RelevantRootInput (L := L) (hL := hL)).LV) := by
          simpa [q] using hz
        exact hyNotC (hzEq ▸ hzC)
      old_not_mem := hyNotC }
  apply hnoEscape
  refine ⟨y, ?_, ⟨E⟩⟩
  simpa only [y, ← hfirst] using P.path.initial_mem_support

/-- A grounded finite source cannot simultaneously be a target marker.
The former lies on an inessential recorded component and the latter on an
essential limiting component. -/
theorem splitGrounded_finiteSource_not_mem_targetMarkers
    {x : V}
    (hxFinite : x ∈ (RelevantRootInput (L := L) (hL := hL)).finiteSource)
    (hxTarget : x ∈ (RelevantRootInput (L := L) (hL := hL)).targetMarkers) :
    False := by
  change x ∈ L.groundedFiniteTerminalSet at hxFinite
  obtain ⟨a, _ha, p, hchosen, hpTerminal⟩ := hxFinite
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  obtain ⟨q, hqEssential, hxQ⟩ := hxTarget.2
  exact (Gamma.not_mem_inessentialPaths_of_intersects_essential
    (hL.legal.warpStages (Ladder.finalStage kappa)) hqEssential
      ⟨x, Gamma.terminal_mem_support hpTerminal, hxQ⟩) hpInessential

namespace SplitGroundedUnusedRecord

/-- Exact root-failure alternatives for a relevant blocking fragment.
There is no escape-free reserved alternative: a relevant escape-free owner
is essential, whereas the reserved record is inessential. -/
inductive SplitGroundedRelevantBlockingRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (P : (RelevantRootInput (L := L) (hL := hL)).Fragment) : Prop
  | reservedEscape
      (parent_eq : P.parent = R.record)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (RelevantRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RelevantRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | hangingEscape
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (RelevantRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RelevantRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | deleted
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (segment_finish : segment.finish = GroundingCut.blockingPoint
        (RelevantRootInput (L := L) (hL := hL)) S.cut P)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (RelevantRootEdges (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RelevantRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a lastDeleted.head)
      (deleted_class : SplitGroundedReducedDeletedClassAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T segment lastDeleted)

/-- Refine the already checked reduced root normal form using the exact
membership disjunction of `splitGroundedRelevantG0`. -/
theorem relevantBlockingPointRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (P : (RelevantRootInput (L := L) (hL := hL)).Fragment)
    (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RelevantRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a
        (GroundingCut.blockingPoint
          (RelevantRootInput (L := L) (hL := hL)) S.cut P))
    (hcontrol : ∀ c : ControlRequest
        (RelevantRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RelevantRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    SplitGroundedRelevantBlockingRootFailureAt R T P := by
  have old := R.reducedBlockingPointRootFailureAt T P hP.1 hnot hcontrol
  cases old with
  | reservedEscape parent_eq initial_eq meets_escape initial_not_rooted =>
      exact .reservedEscape parent_eq initial_eq meets_escape initial_not_rooted
  | reservedTerminal parent_eq initial_eq terminal terminal_eq
      not_meets_escape initial_not_rooted =>
      have hessential :=
        L.splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
          hL.legal S.cut P hP not_meets_escape
      rw [parent_eq] at hessential
      change R.record ∈ Gamma.essentialWarpPart L.limitWarp at hessential
      exact (R.limit_inessential.2 hessential).elim
  | hangingEscape parent_hanging initial_eq meets_escape initial_not_rooted =>
      exact .hangingEscape parent_hanging initial_eq meets_escape
        initial_not_rooted
  | hangingTerminal parent_hanging initial_eq terminal terminal_eq
      not_meets_escape initial_not_rooted =>
      have hessential :=
        L.splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
          hL.legal S.cut P hP not_meets_escape
      have htarget := splitGrounded_hangingEssential_initial_mem_targetMarkers
        P hessential parent_hanging
      have hCV := splitGrounded_hangingEssentialFirst_notEscape_initial_mem_CV
        P hessential parent_hanging initial_eq not_meets_escape
      rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit hCV with
          hfinite | ⟨r, hrAux, hrExit⟩
      · exact (splitGrounded_finiteSource_not_mem_targetMarkers
          hfinite (initial_eq ▸ htarget)).elim
      · apply False.elim
        apply initial_not_rooted
        let c : ControlRequest
            (RelevantRootInput (L := L) (hL := hL)) S.cut :=
          ⟨P.path.initial, ⟨r, by simpa only [hrExit]⟩⟩
        exact hcontrol c
  | deleted segment segment_start segment_finish segment_support segment_edges
      lastDeleted head_not_rooted deleted_class =>
      exact .deleted segment segment_start segment_finish segment_support
        segment_edges lastDeleted head_not_rooted deleted_class

end SplitGroundedUnusedRecord

/-- Total owner-level normal form for an unrooted point of the filtered
boundary. -/
inductive SplitGroundedRelevantBBRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) (t : V) : Prop
  | finite
      (ht : t ∈ (RelevantRootInput (L := L) (hL := hL)).finiteSource)
      (data : SplitGroundedUnusedRecord.SplitGroundedReducedFiniteSourceRootFailureAt
        R T t ht)
  | blocking
      (P : (RelevantRootInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (RelevantRootInput (L := L) (hL := hL)) S.cut P = t)
      (data : SplitGroundedUnusedRecord.SplitGroundedRelevantBlockingRootFailureAt
        R T P)

/-- Normalize one unrooted relevant-boundary point in the actual relation
stopped at `T`. -/
theorem SplitGroundedUnusedRecord.relevantBBRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {t : V}
    (ht : t ∈ L.splitGroundedRelevantBB hL.legal S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RelevantRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t)
    (hcontrol : ∀ c : ControlRequest
        (RelevantRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RelevantRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    SplitGroundedRelevantBBRootFailureAt R T t := by
  cases L.splitGroundedRelevantBBPointOwner_of_mem ht with
  | finiteSource hfinite hcut =>
      exact .finite hfinite
        (R.finiteSourceRootFailureAt T hfinite hcut hnot hcontrol).some
  | oldControl old value_eq =>
      exfalso
      apply hnot
      simpa only [← value_eq, oldRequestControl_val] using
        hcontrol (oldRequestControl old)
  | blocking P hP point_eq _point_mem_support =>
      have hnotP : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ RelevantRootEdges
              (L := L) (hL := hL) (hground := hground)
                (S := S) (K := K) T) a
            (GroundingCut.blockingPoint
              (RelevantRootInput (L := L) (hL := hL)) S.cut P) := by
        simpa only [point_eq] using hnot
      exact .blocking P hP point_eq
        (R.relevantBlockingPointRootFailureAt T P hP hnotP hcontrol)

/-- Pointwise totalization over an arbitrary final frontier contained in
the relevant boundary. -/
theorem SplitGroundedUnusedRecord.relevantFrontier_rootedAt_or_failure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hT : T ⊆ L.splitGroundedRelevantBB hL.legal S.cut)
    (hcontrol : ∀ c : ControlRequest
        (RelevantRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RelevantRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    (∀ t ∈ T, ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RelevantRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t) ∨
      ∃ t ∈ T, SplitGroundedRelevantBBRootFailureAt R T t := by
  classical
  by_cases hall : ∀ t ∈ T, ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RelevantRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨t, ht, hnot⟩ := hall
    have hnot' : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RelevantRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a t := by
      rintro ⟨a, ha, hareach⟩
      exact hnot a ha hareach
    exact ⟨t, ht, R.relevantBBRootFailureAt T (hT ht) hnot' hcontrol⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.relevantBlockingPointRootFailureAt
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.relevantBBRootFailureAt
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.relevantFrontier_rootedAt_or_failure
