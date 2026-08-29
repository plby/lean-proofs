/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstRank

/-!
# Simultaneous finite prefixes for the old-request matching

The old-request dependency is already a depth-one partial matching.  This
file uses that proved matching, rather than assuming a simultaneous choice,
to assemble all of its finite source-prefix contributions at once.

One canonical witness is chosen for each literal dependency edge.  Its
maximal source-first boundary determines the edge injectively, so distinct
edges have disjoint prefix warps.  Their union is therefore an actual warp;
all its members start in the ambient source, it roots every source-first
obligation on every matched sacrificed owner, and it is disjoint from the
globally reserved record.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

namespace ReservedStrongSelectedStartingLastContact.SourceSaturation

/-- Literal edges of the proved old-request dependency relation. -/
def OldRequestForkEdge :=
  {e : Request J S.cut × Request J S.cut //
    OldRequestForkDependency
      (L := L) (hL := hL) (S := S) e.1 e.2}

/-- The concrete last-contact and finite-suffix witnesses attached to one
dependency edge.  This structure merely repackages the existential defining
`OldRequestForkDependency`; it adds no matching or coverage field. -/
structure OldRequestForkWitness
    (e : OldRequestForkEdge (L := L) (hL := hL) (S := S)) where
  X : ReservedStrongSelectedStartingLastContact
    (L := L) (hL := hL) (S := S) e.1.1
  saturation : SourceSaturation X
  finalPrefix : LastSourceFirstPrefix saturation
  suffix : FiniteTrace Gamma.graph
  suffix_eq : saturation.normalizedSuffix.path = .finite suffix
  apex_eq : requestAuxVertex e.1.2 = .old finalPrefix.boundary
  exit_eq : requestExit e.1.2 = finalPrefix.boundary

/-- Every dependency edge has its displayed concrete witness. -/
theorem oldRequestForkWitness_nonempty
    (e : OldRequestForkEdge (L := L) (hL := hL) (S := S)) :
    Nonempty (OldRequestForkWitness e) := by
  obtain ⟨X, D, F, Q, hQ, hapex, hexit⟩ := e.property
  exact ⟨⟨X, D, F, Q, hQ, hapex, hexit⟩⟩

/-- A fixed canonical witness for each actual dependency edge. -/
noncomputable def oldRequestForkWitness
    (e : OldRequestForkEdge (L := L) (hL := hL) (S := S)) :
    OldRequestForkWitness e :=
  Classical.choice (oldRequestForkWitness_nonempty e)

namespace OldRequestForkWitness

/-- The actual endpoint transfer at the target request of this dependency. -/
noncomputable def transfer
    {e : OldRequestForkEdge (L := L) (hL := hL) (S := S)}
    (A : OldRequestForkWitness e) :
    A.finalPrefix.RequestExitTransfer e.1.2 :=
  Classical.choice
    (A.finalPrefix.exists_requestExitTransfer e.1.2 A.exit_eq)

/-- Every finite prefix contributed by one matched transfer starts at an
ambient source. -/
theorem prefixWarp_member_initial_mem_source
    {e : OldRequestForkEdge (L := L) (hL := hL) (S := S)}
    (A : OldRequestForkWitness e) {p : Gamma.DPath}
    (hp : p ∈ A.transfer.prefixWarp) :
    p.initial ∈ Gamma.source := by
  cases htransfer : A.transfer with
  | ownStarting Y =>
      rw [htransfer] at hp
      simp only [LastSourceFirstPrefix.RequestExitTransfer.prefixWarp,
        Set.mem_singleton_iff] at hp
      subst p
      exact Y.oldPrefix_source
  | sourceSaturated Y E =>
      rw [htransfer] at hp
      simp only [LastSourceFirstPrefix.RequestExitTransfer.prefixWarp,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact Y.oldPrefix_source
      · exact E.prefix_source

/-- The finite prefix contribution itself roots every required source-first
point on the matched sacrificed owner. -/
theorem prefixWarp_roots_every_owner_boundary
    {e : OldRequestForkEdge (L := L) (hL := hL) (S := S)}
    (A : OldRequestForkWitness e) {z : V}
    (hz : z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hzOwner : z ∈ A.saturation.owner.support) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          Alternating.familyEdges A.transfer.prefixWarp) a z := by
  cases htransfer : A.transfer with
  | ownStarting Y _ owner_eq contact_eq _ =>
      have hpStart : Y.oldPrefix.start = A.saturation.owner.initial := by
        rw [owner_eq]
        exact Y.oldPrefix_start
      have hpFinish : Y.oldPrefix.finish = A.finalPrefix.boundary :=
        Y.oldPrefix_finish.trans contact_eq
      have hpEdges : Y.oldPrefix.edgeSet ⊆
          A.saturation.owner.edgeSet := by
        rw [owner_eq]
        exact Y.oldPrefix_edges
      obtain ⟨a, ha, hreach⟩ :=
        LastSourceFirstPrefix.RequestExitTransfer.reaches_every_owner_boundary_of_prefix
          A.finalPrefix Y.oldPrefix hpStart Y.oldPrefix_source hpFinish
            hpEdges hz hzOwner
      refine ⟨a, ha, Relation.ReflTransGen.mono ?_ a z hreach⟩
      intro x y hxy
      simp only [LastSourceFirstPrefix.RequestExitTransfer.prefixWarp,
        Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨(.inl Y.oldPrefix : Gamma.DPath), Set.mem_singleton _, hxy⟩
  | sourceSaturated Y E _ _ contact_eq owner_eq _ =>
      have hpStart : E.ownerPrefix.start = A.saturation.owner.initial := by
        rw [← owner_eq]
        exact E.prefix_start
      have hpFinish : E.ownerPrefix.finish = A.finalPrefix.boundary :=
        E.prefix_finish.trans contact_eq
      have hpEdges : E.ownerPrefix.edgeSet ⊆
          A.saturation.owner.edgeSet := by
        rw [← owner_eq]
        exact E.prefix_edges
      obtain ⟨a, ha, hreach⟩ :=
        LastSourceFirstPrefix.RequestExitTransfer.reaches_every_owner_boundary_of_prefix
          A.finalPrefix E.ownerPrefix hpStart E.prefix_source hpFinish
            hpEdges hz hzOwner
      refine ⟨a, ha, Relation.ReflTransGen.mono ?_ a z hreach⟩
      intro x y hxy
      simp only [LastSourceFirstPrefix.RequestExitTransfer.prefixWarp,
        Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨(.inl E.ownerPrefix : Gamma.DPath),
        Set.mem_insert_of_mem _ (Set.mem_singleton _), hxy⟩

end OldRequestForkWitness

/-- The maximal source-first boundary identifies a dependency edge.  Target
request injectivity identifies the right endpoint; left uniqueness of the
proved dependency matching then identifies the producer. -/
theorem oldRequestForkWitness_boundary_injective :
    Function.Injective (fun e :
      OldRequestForkEdge (L := L) (hL := hL) (S := S) ↦
        (oldRequestForkWitness e).finalPrefix.boundary) := by
  intro e f hboundary
  let A := oldRequestForkWitness e
  let B := oldRequestForkWitness f
  have htarget : e.1.2 = f.1.2 := by
    apply GroundingSelection.requestAuxVertex_injective
    calc
      requestAuxVertex e.1.2 = .old A.finalPrefix.boundary := A.apex_eq
      _ = .old B.finalPrefix.boundary := congrArg _ hboundary
      _ = requestAuxVertex f.1.2 := B.apex_eq.symm
  have hsource : e.1.1 = f.1.1 := by
    apply oldRequestForkDependency_leftUnique e.property
    simpa only [htarget] using f.property
  apply Subtype.ext
  exact Prod.ext hsource htarget

/-- Chosen prefix contributions of distinct matching edges are disjoint. -/
theorem oldRequestForkWitness_prefixWarp_disjoint
    {e f : OldRequestForkEdge (L := L) (hL := hL) (S := S)}
    (hef : e ≠ f) :
    Disjoint
      (Gamma.vertexSet (oldRequestForkWitness e).transfer.prefixWarp)
      (Gamma.vertexSet (oldRequestForkWitness f).transfer.prefixWarp) := by
  let A := oldRequestForkWitness e
  let B := oldRequestForkWitness f
  apply A.transfer.disjoint_prefixWarp_of_boundary_ne B.transfer
  intro hboundary
  exact hef (oldRequestForkWitness_boundary_injective hboundary)

/-- The simultaneous finite-prefix family contributed by every actual
old-request dependency edge. -/
def oldRequestForkPrefixWarp : Set Gamma.DPath :=
  ⋃ e : OldRequestForkEdge (L := L) (hL := hL) (S := S),
    (oldRequestForkWitness e).transfer.prefixWarp

/-- The union over the proved partial matching is an actual warp. -/
theorem oldRequestForkPrefixWarp_isWarp :
    Gamma.IsWarp (oldRequestForkPrefixWarp
      (L := L) (hL := hL) (S := S)) := by
  intro p hp q hq hpq
  simp only [oldRequestForkPrefixWarp, Set.mem_iUnion] at hp hq
  obtain ⟨e, hp⟩ := hp
  obtain ⟨f, hq⟩ := hq
  by_cases hef : e = f
  · subst f
    exact (oldRequestForkWitness e).transfer.prefixWarp_isWarp hp hq hpq
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.mp
      (oldRequestForkWitness_prefixWarp_disjoint hef)
        ⟨p, hp, hxp⟩ ⟨q, hq, hxq⟩

/-- Every component of the simultaneous matching prefix warp starts in the
ambient source. -/
theorem oldRequestForkPrefixWarp_initial_subset_source :
    Gamma.initialSet (oldRequestForkPrefixWarp
      (L := L) (hL := hL) (S := S)) ⊆ Gamma.source := by
  rintro x ⟨p, hp, rfl⟩
  simp only [oldRequestForkPrefixWarp, Set.mem_iUnion] at hp
  obtain ⟨e, hp⟩ := hp
  exact (oldRequestForkWitness e).prefixWarp_member_initial_mem_source hp

/-- Each matched sacrificed owner has all of its required source-first
points rooted in the one simultaneous prefix warp. -/
theorem oldRequestForkPrefixWarp_roots_owner_boundaries
    (e : OldRequestForkEdge (L := L) (hL := hL) (S := S))
    {z : V}
    (hz : z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hzOwner : z ∈ (oldRequestForkWitness e).saturation.owner.support) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ Alternating.familyEdges
          (oldRequestForkPrefixWarp (L := L) (hL := hL) (S := S))) a z := by
  obtain ⟨a, ha, hreach⟩ :=
    (oldRequestForkWitness e).prefixWarp_roots_every_owner_boundary
      hz hzOwner
  refine ⟨a, ha, Relation.ReflTransGen.mono ?_ a z hreach⟩
  intro x y hxy
  simp only [Alternating.familyEdges, Set.mem_iUnion] at hxy ⊢
  obtain ⟨p, hp, he⟩ := hxy
  exact ⟨p, Set.mem_iUnion.2 ⟨e, hp⟩, he⟩

/-- The entire simultaneous matching prefix warp is disjoint from the
globally reserved record. -/
theorem oldRequestForkPrefixWarp_disjoint_reservedRecord :
    Disjoint
      (Gamma.vertexSet (oldRequestForkPrefixWarp
        (L := L) (hL := hL) (S := S)))
      (canonicalReservedRecord L hL S).record.support := by
  rw [Set.disjoint_left]
  intro x hx hreserved
  obtain ⟨p, hp, hxp⟩ := hx
  simp only [oldRequestForkPrefixWarp, Set.mem_iUnion] at hp
  obtain ⟨e, hp⟩ := hp
  let A := oldRequestForkWitness e
  rcases A.transfer.prefixWarp_member_carrier hp with hpStart | hpOwner
  · have hstartLimit :
        (reservedStrongSelectedStartingRecord e.1.2).record ∈ L.limitWarp := by
      simpa only [popularAuxiliaryInput, limitWarp] using
        (reservedStrongSelectedStartingRecord e.1.2).record_mem_ladder
    have hreservedLimit :
        (canonicalReservedRecord L hL S).record ∈ L.limitWarp :=
      (canonicalReservedRecord L hL S).limit_inessential.1
    have hne : (reservedStrongSelectedStartingRecord e.1.2).record ≠
        (canonicalReservedRecord L hL S).record :=
      (canonicalReservedRecord_ne_reservedStrongSelectedStartingRecord
        e.1.2).symm
    have hwarp : Gamma.IsWarp L.limitWarp := by
      simpa only [popularAuxiliaryInput, limitWarp] using (J).ladder.disjoint
    exact Set.disjoint_left.mp
      (hwarp hstartLimit hreservedLimit hne) (hpStart hxp) hreserved
  · have hownerLimit : A.saturation.owner ∈ L.limitWarp :=
      A.finalPrefix.owner_mem_limitWarp
    have hreservedLimit :
        (canonicalReservedRecord L hL S).record ∈ L.limitWarp :=
      (canonicalReservedRecord L hL S).limit_inessential.1
    have hne : A.saturation.owner ≠
        (canonicalReservedRecord L hL S).record := by
      intro hEq
      have hbRelevant : A.finalPrefix.boundary ∈
          reservedStrongSelectedRelevantBB
            (L := L) (hL := hL) (S := S) :=
        reservedStrongSelectedSourceFirstBB_subset_relevantBB
          A.finalPrefix.boundary_mem
      have hbReserved : A.finalPrefix.boundary ∈
          (canonicalReservedRecord L hL S).record.support := by
        rw [← hEq]
        exact A.finalPrefix.boundary_mem_owner
      exact Set.disjoint_left.mp
        canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
          hbRelevant hbReserved
    have hwarp : Gamma.IsWarp L.limitWarp := by
      simpa only [popularAuxiliaryInput, limitWarp] using (J).ladder.disjoint
    exact Set.disjoint_left.mp
      (hwarp hownerLimit hreservedLimit hne) (hpOwner hxp) hreserved

/-- Consequently the globally reserved record can be adjoined to the whole
old-request matching prefix warp without any further compatibility choice. -/
theorem insert_reservedRecord_oldRequestForkPrefixWarp_isWarp :
    Gamma.IsWarp
      (insert (canonicalReservedRecord L hL S).record
        (oldRequestForkPrefixWarp (L := L) (hL := hL) (S := S))) := by
  intro p hp q hq hpq
  rcases hp with rfl | hp <;> rcases hq with rfl | hq
  · exact False.elim (hpq rfl)
  · change Disjoint
      (canonicalReservedRecord L hL S).record.support q.support
    rw [Set.disjoint_left]
    intro x hxReserved hxq
    exact Set.disjoint_left.mp
      oldRequestForkPrefixWarp_disjoint_reservedRecord
        ⟨q, hq, hxq⟩ hxReserved
  · change Disjoint p.support
      (canonicalReservedRecord L hL S).record.support
    rw [Set.disjoint_left]
    intro x hxp hxReserved
    exact Set.disjoint_left.mp
      oldRequestForkPrefixWarp_disjoint_reservedRecord
        ⟨p, hp, hxp⟩ hxReserved
  · exact oldRequestForkPrefixWarp_isWarp hp hq hpq

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.oldRequestForkPrefixWarp_isWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.oldRequestForkPrefixWarp_roots_owner_boundaries
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.insert_reservedRecord_oldRequestForkPrefixWarp_isWarp
