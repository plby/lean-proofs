/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedCanonicalSimultaneous
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparator818

/-!
# Source-reachable boundary outcomes for the grounded split switch

The literal set `BB` contains bookkeeping points on hanging components
which no original source can reach.  Such points are irrelevant to ambient
source--target separation and must not be imposed as false rooting
obligations.  We therefore intersect `BB` with the vertices carrying an
ambient finite source prefix.  The restricted set still separates, and any
remaining root or antichain obstruction retains the concrete ambient
prefixes needed by the subsequent exchange.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath GroundingErasedDecode GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev GroundedReachableInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedReachableIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev GroundedReachableControls :=
  L.splitGroundedCanonicalControls hL hground S

private abbrev GroundedReachableEdges :=
  L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅

/-- Vertices with a finite ambient path from an original source. -/
def splitGroundedAmbientSourceReachable (Gamma : DWeb V) : Set V :=
  {x | ∃ p : FinitePath Gamma.graph,
    p.start ∈ Gamma.source ∧ p.finish = x}

/-- The source-relevant part of the literal grounded boundary. -/
def splitGroundedReachableBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) : Set V :=
  GroundingCut.BB (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut ∩
    splitGroundedAmbientSourceReachable Gamma

theorem splitGroundedReachableBB_subset_BB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    L.splitGroundedReachableBB hL hground S ⊆
      GroundingCut.BB
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut :=
  Set.inter_subset_left

/-- Restricting to ambient-source-reachable boundary points preserves
source--target separation: a source--target path supplies its own prefix to
any contact given by split Assertion 8.18. -/
theorem splitGroundedReachableBB_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Popular.IsSeparator Gamma (L.splitGroundedReachableBB hL hground S) := by
  intro p hpSource hpTarget
  obtain ⟨x, hxp, hxBB⟩ :=
    L.splitGroundedAssertion8_18 hL.legal S.cut S.separates
      p hpSource hpTarget
  obtain ⟨q, hqStart, hqFinish, _hqSupport, _hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (.inl p : Gamma.DPath) (by
        change x ∈ p.support
        exact hxp)
  refine ⟨x, hxp, hxBB, q, ?_, hqFinish⟩
  simpa only [hqStart, DirectedPath.Path.initial] using hpSource

/-- A source-relevant boundary point which is reachable from the full
source but not from the allowed source set after reserving one record. -/
structure SplitGroundedReachableReservedRootObstruction
    (R : L.SplitGroundedUnusedRecord hL hground S
      (GroundedReachableControls (L := L) (hL := hL)
        (hground := hground) (S := S))) where
  boundary : V
  boundary_mem : boundary ∈ L.splitGroundedReachableBB hL hground S
  rooted_from_source : ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ GroundedReachableEdges
        (L := L) (hL := hL) (hground := hground) (S := S)) a boundary
  all_boundary_rooted_from_source : ∀ b ∈
      L.splitGroundedReachableBB hL hground S,
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ GroundedReachableEdges
          (L := L) (hL := hL) (hground := hground) (S := S)) a b
  not_rooted_from_allowed : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ GroundedReachableEdges
        (L := L) (hL := hL) (hground := hground) (S := S)) a boundary

/-- A source-relevant boundary point not reached from any original source
by the canonical pre-stopped relation. -/
structure SplitGroundedReachableWholeSourceRootObstruction
    (R : L.SplitGroundedUnusedRecord hL hground S
      (GroundedReachableControls (L := L) (hL := hL)
        (hground := hground) (S := S))) where
  boundary : V
  boundary_mem : boundary ∈ L.splitGroundedReachableBB hL hground S
  not_rooted : ¬ ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ GroundedReachableEdges
        (L := L) (hL := hL) (hground := hground) (S := S)) a boundary

/-- Two distinct source-relevant boundary points occurring in order in one
canonical pre-stopped component.  Both endpoints retain allowed roots and
ambient source prefixes through membership in the restricted boundary. -/
structure SplitGroundedReachableBoundaryObstruction
    (R : L.SplitGroundedUnusedRecord hL hground S
      (GroundedReachableControls (L := L) (hL := hL)
        (hground := hground) (S := S))) where
  earlier : V
  later : V
  earlier_mem : earlier ∈ L.splitGroundedReachableBB hL hground S
  later_mem : later ∈ L.splitGroundedReachableBB hL hground S
  distinct : earlier ≠ later
  reaches : Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈ GroundedReachableEdges
      (L := L) (hL := hL) (hground := hground) (S := S)) earlier later
  earlier_rooted : ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ GroundedReachableEdges
        (L := L) (hL := hL) (hground := hground) (S := S)) a earlier
  later_rooted : ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ GroundedReachableEdges
        (L := L) (hL := hL) (hground := hground) (S := S)) a later

namespace SplitGroundedReachableWholeSourceRootObstruction

theorem exists_ambientPath_to_boundary
    (O : L.SplitGroundedReachableWholeSourceRootObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)) :
    ∃ p : FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.boundary :=
  O.boundary_mem.2

end SplitGroundedReachableWholeSourceRootObstruction

namespace SplitGroundedReachableReservedRootObstruction

theorem exists_ambientPath_to_boundary
    (O : L.SplitGroundedReachableReservedRootObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)) :
    ∃ p : FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.boundary :=
  O.boundary_mem.2

/-- The only possible full-source root of a reserved-source obstruction is
the deliberately omitted record initial. -/
theorem reached_from_reserved
    (O : L.SplitGroundedReachableReservedRootObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ L.splitGroundedCanonicalSwitchedEdgesAt
        hL hground S ∅)
      (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial
      O.boundary := by
  obtain ⟨a, ha, hab⟩ := O.rooted_from_source
  by_cases hae : a =
      (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial
  · simpa only [hae] using hab
  · exfalso
    apply O.not_rooted_from_allowed
    exact ⟨a, ⟨ha, by simpa only [Set.mem_singleton_iff] using hae⟩, hab⟩

end SplitGroundedReachableReservedRootObstruction

namespace SplitGroundedReachableBoundaryObstruction

theorem exists_ambientPath_to_earlier
    (O : L.SplitGroundedReachableBoundaryObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)) :
    ∃ p : FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.earlier :=
  O.earlier_mem.2

theorem exists_ambientPath_to_later
    (O : L.SplitGroundedReachableBoundaryObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)) :
    ∃ p : FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.later :=
  O.later_mem.2

end SplitGroundedReachableBoundaryObstruction

/-- Total source-faithful outcome for the canonical grounded switch.  The
success branch is an exact Assertion 8.22 output; all failures retain the
ambient source prefixes intentionally absent from the literal full-`BB`
formulation. -/
theorem splitGroundedCanonicalAssertion822Output_or_reachableObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.SplitGroundedReachableReservedRootObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) ∨
      Nonempty (L.SplitGroundedReachableWholeSourceRootObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) ∨
      Nonempty (L.SplitGroundedReachableBoundaryObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) := by
  classical
  let R := L.splitGroundedCanonicalUnusedRecord hL hground S
  let B := L.splitGroundedReachableBB hL hground S
  let E := L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅
  by_cases hrootSource : ∀ b ∈ B, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
  · by_cases hrootAllowed : ∀ b ∈ B,
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
    · by_cases hanti : IsReachabilityAntichain E B
      · left
        apply GroundingAssertion822Output.exists_of_rootedReachability
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut E
          (Gamma.source \ {R.record.initial}) B
        · exact L.splitGroundedCanonicalSwitchedEdgesAt_subset_adj
            hL hground S ∅
        · exact L.splitGroundedCanonicalSwitchedEdgesAt_biUnique
            hL hground S ∅
        · exact Set.sdiff_subset
        · exact L.splitGroundedReachableBB_subset_BB hL hground S
        · exact L.splitGroundedReachableBB_isSeparator hL hground S
        · exact hanti
        · exact hrootAllowed
        · exact R.grounded
        · simp
      · right
        right
        right
        by_contra hnone
        apply hanti
        intro b hb c hc hbc
        by_contra hne
        exact hnone ⟨{
          earlier := b
          later := c
          earlier_mem := hb
          later_mem := hc
          distinct := hne
          reaches := hbc
          earlier_rooted := by
            obtain ⟨a, ha, hab⟩ := hrootAllowed b hb
            exact ⟨a, ha.1, hab⟩
          later_rooted := by
            obtain ⟨a, ha, hac⟩ := hrootAllowed c hc
            exact ⟨a, ha.1, hac⟩ }⟩
    · right
      left
      push Not at hrootAllowed
      obtain ⟨b, hb, hbnot⟩ := hrootAllowed
      exact ⟨{
        boundary := b
        boundary_mem := hb
        rooted_from_source := hrootSource b hb
        all_boundary_rooted_from_source := hrootSource
        not_rooted_from_allowed := by
          rintro ⟨a, ha, hab⟩
          exact hbnot a ha hab }⟩
  · right
    right
    left
    push Not at hrootSource
    obtain ⟨b, hb, hbnot⟩ := hrootSource
    exact ⟨{
      boundary := b
      boundary_mem := hb
      not_rooted := by
        rintro ⟨a, ha, hab⟩
        exact hbnot a ha hab }⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedReachableBB_isSeparator
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReachableReservedRootObstruction.reached_from_reserved
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedCanonicalAssertion822Output_or_reachableObstruction
