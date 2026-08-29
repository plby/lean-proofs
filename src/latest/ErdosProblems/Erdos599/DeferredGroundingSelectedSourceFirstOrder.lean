/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceSaturation
import ErdosProblems.Erdos599.SafeSwitchingArbitraryReference

/-!
# Source-first boundary order under source-owner saturation

When the terminal-contact transaction truncates a source-grounded reference
owner at its final route contact, a required source-first boundary point on
that owner has only two possible locations.  It is either already on the
retained source prefix, or it lies strictly after the contact.  The latter
case carries the literal owner interval and a strict natural-number prefix
measure, so it cannot be treated as an anonymous displaced sink.
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
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

namespace ReservedStrongSelectedStartingLastContact.SourceSaturation

/-- Coordinate form of the fact that a walk starting at a point of a finite
simple path and using only its directed edges follows the same consecutive
vertices. -/
theorem walk_getElem_eq_finite_start_add
    (p : FinitePath Gamma.graph) {a b : V}
    (w : Walk Gamma.graph a b) (hE : w.edgeSet ⊆ p.edgeSet)
    (s : ℕ) (hs : s < p.walk.support.length)
    (hstart : a = p.walk.support[s]) :
    ∀ n (hn : n ≤ w.length),
      ∃ h : s + n < p.walk.support.length,
        w.support[n]'(by rw [Walk.support_length_eq]; omega) =
          p.walk.support[s + n] := by
  intro n hn
  induction n with
  | zero =>
      refine ⟨by simpa using hs, ?_⟩
      have hzero : w.support[0]'(by
          rw [Walk.support_length_eq]
          omega) = a := by
        exact (List.getElem_zero (by
          rw [Walk.support_length_eq]
          omega)).trans w.head_support
      simpa using hzero.trans hstart
  | succ n ih =>
      have hnlt : n < w.length := by omega
      have hn0 : n < w.support.length := by
        rw [Walk.support_length_eq]
        omega
      have hn1 : n + 1 < w.support.length := by
        rw [Walk.support_length_eq]
        omega
      have hedge : (w.support[n], w.support[n + 1]) ∈ w.edgeSet := by
        rw [Walk.mem_edgeSet_iff_exists_getElem]
        exact ⟨n, hn1, rfl⟩
      obtain ⟨j, hj, hja, hjb⟩ :=
        p.walk.exists_adjacent_getElem_of_mem_edgeSet (hE hedge)
      obtain ⟨hnAmbient, hnEq⟩ := ih (by omega)
      have hjEq : j = s + n := by
        have hfin : (⟨j, by omega⟩ : Fin p.walk.support.length) =
            ⟨s + n, hnAmbient⟩ := by
          apply p.isPath.get_inj_iff.mp
          simpa using hja.trans hnEq
        exact congrArg Fin.val hfin
      subst j
      refine ⟨by simpa [Nat.add_assoc] using hj, ?_⟩
      simpa [Nat.add_assoc] using hjb.symm

/-- A finite initial subpath reaches its endpoint at the ambient path index
equal to its edge length. -/
theorem initialSubpath_finish_occursAt_length
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hstart : q.start = P.initial) (hE : q.edgeSet ⊆ P.edgeSet) :
    GroundingCut.OccursAt P q.walk.length q.finish := by
  cases P with
  | inl p =>
      change q.start = p.start at hstart
      change q.edgeSet ⊆ p.edgeSet at hE
      have hp0 : 0 < p.walk.support.length := p.support_length_pos
      have hstart0 : q.start = p.walk.support[0] := by
        exact hstart.trans p.support_getElem_zero.symm
      obtain ⟨hbound, hmap⟩ :=
        walk_getElem_eq_finite_start_add p q.walk hE 0 hp0 hstart0
          q.walk.length le_rfl
      refine ⟨by simpa using hbound, ?_⟩
      have hqLen : q.walk.length < q.walk.support.length := by
        rw [Walk.support_length_eq]
        omega
      have hfinish : q.walk.support[q.walk.length]'hqLen = q.finish :=
        Alternating.Walk.getElem_length_eq_end q.walk
      simpa using hmap.symm.trans hfinish
  | inr ray =>
      change q.start = ray 0 at hstart
      change q.edgeSet ⊆ ray.edgeSet at hE
      change ray q.walk.length = q.finish
      have hmap :=
        Alternating.SwitchingCore.ArbitraryReference.Walk.getElem_eq_ray_start_add
          q.walk ray hE 0 hstart q.walk.length le_rfl
      have hqLen : q.walk.length < q.walk.support.length := by
        rw [Walk.support_length_eq]
        omega
      have hfinish : q.walk.support[q.walk.length]'hqLen = q.finish :=
        Alternating.Walk.getElem_length_eq_end q.walk
      simpa using hmap.symm.trans hfinish

/-- Intrinsic order of the endpoints of two finite initial subpaths is
exactly weak order of their lengths. -/
theorem initialSubpath_length_le_of_beforeEq_finish
    (P : Gamma.DPath) (q r : FinitePath Gamma.graph)
    (hqStart : q.start = P.initial) (hrStart : r.start = P.initial)
    (hqEdges : q.edgeSet ⊆ P.edgeSet)
    (hrEdges : r.edgeSet ⊆ P.edgeSet)
    (hbefore : GroundingCut.BeforeEq P q.finish r.finish) :
    q.walk.length ≤ r.walk.length := by
  rcases hbefore with ⟨m, n, hmq, hnr, hmn⟩
  have hqOccurs :=
    initialSubpath_finish_occursAt_length P q hqStart hqEdges
  have hrOccurs :=
    initialSubpath_finish_occursAt_length P r hrStart hrEdges
  have hqm : q.walk.length = m :=
    GroundingCutDecoder.occursAt_index_injective hqOccurs hmq
  have hrn : r.walk.length = n :=
    GroundingCutDecoder.occursAt_index_injective hrOccurs hnr
  simpa only [hqm, hrn] using hmn

/-- Strict intrinsic order of two initial-subpath endpoints gives strict
order of their lengths. -/
theorem initialSubpath_length_lt_of_before_finish
    (P : Gamma.DPath) (q r : FinitePath Gamma.graph)
    (hqStart : q.start = P.initial) (hrStart : r.start = P.initial)
    (hqEdges : q.edgeSet ⊆ P.edgeSet)
    (hrEdges : r.edgeSet ⊆ P.edgeSet)
    (hbefore : GroundingCut.Before P q.finish r.finish) :
    q.walk.length < r.walk.length := by
  have hle := initialSubpath_length_le_of_beforeEq_finish
    P q r hqStart hrStart hqEdges hrEdges hbefore.1
  apply lt_of_le_of_ne hle
  intro hlen
  apply hbefore.2
  have hqOccurs :=
    initialSubpath_finish_occursAt_length P q hqStart hqEdges
  have hrOccurs :=
    initialSubpath_finish_occursAt_length P r hrStart hrEdges
  rw [hlen] at hqOccurs
  cases P with
  | inl p =>
      rcases hqOccurs with ⟨hqBound, hqValue⟩
      rcases hrOccurs with ⟨hrBound, hrValue⟩
      exact hqValue.symm.trans hrValue
  | inr ray =>
      exact hqOccurs.symm.trans hrOccurs

/-- Two finite initial subpaths of one finite path or ray are literally
ordered prefixes whenever their lengths are ordered. -/
theorem initialSubpath_isPrefixOf_of_length_le
    (P : Gamma.DPath) (q r : FinitePath Gamma.graph)
    (hqStart : q.start = P.initial) (hrStart : r.start = P.initial)
    (hqEdges : q.edgeSet ⊆ P.edgeSet)
    (hrEdges : r.edgeSet ⊆ P.edgeSet)
    (hlen : q.walk.length ≤ r.walk.length) :
    q.IsPrefixOf r := by
  rw [FinitePath.IsPrefixOf, List.prefix_iff_eq_take]
  apply List.ext_getElem
  · rw [List.length_take, Walk.support_length_eq,
      Walk.support_length_eq]
    rw [Nat.min_eq_left]
    omega
  · intro i hiq hitake
    rw [List.getElem_take]
    have hir : i < r.walk.support.length := by
      rw [Walk.support_length_eq] at hiq ⊢
      omega
    cases P with
    | inl p =>
        change q.start = p.start at hqStart
        change r.start = p.start at hrStart
        change q.edgeSet ⊆ p.edgeSet at hqEdges
        change r.edgeSet ⊆ p.edgeSet at hrEdges
        have hp0 : 0 < p.walk.support.length := p.support_length_pos
        have hqStart0 : q.start = p.walk.support[0] := by
          exact hqStart.trans p.support_getElem_zero.symm
        have hrStart0 : r.start = p.walk.support[0] := by
          exact hrStart.trans p.support_getElem_zero.symm
        obtain ⟨_hqi, hqi⟩ :=
          walk_getElem_eq_finite_start_add p q.walk hqEdges 0 hp0
            hqStart0 i (by rw [Walk.support_length_eq] at hiq; omega)
        obtain ⟨_hri, hri⟩ :=
          walk_getElem_eq_finite_start_add p r.walk hrEdges 0 hp0
            hrStart0 i (by rw [Walk.support_length_eq] at hir; omega)
        simpa using hqi.trans hri.symm
    | inr ray =>
        change q.start = ray 0 at hqStart
        change r.start = ray 0 at hrStart
        change q.edgeSet ⊆ ray.edgeSet at hqEdges
        change r.edgeSet ⊆ ray.edgeSet at hrEdges
        have hqi :=
          Alternating.SwitchingCore.ArbitraryReference.Walk.getElem_eq_ray_start_add
            q.walk ray hqEdges 0 hqStart i
              (by rw [Walk.support_length_eq] at hiq; omega)
        have hri :=
          Alternating.SwitchingCore.ArbitraryReference.Walk.getElem_eq_ray_start_add
            r.walk ray hrEdges 0 hrStart i
              (by rw [Walk.support_length_eq] at hir; omega)
        exact hqi.trans hri.symm

/-- A required source-first boundary point on the source-grounded owner
which is truncated by saturation is either reached by the literally retained
owner prefix, or occurs strictly after the splice contact.  The latter case
retains both the old source ancestry and a strict prefix-length potential,
together with the exact discarded owner interval from the contact to the
required point. -/
theorem sourceFirstBoundary_retainedPrefix_or_strictOwnerTail
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hbOwner : b ∈ D.owner.support) :
    (b ∈ reservedStrongSelectedSourceFirstBB
          (L := L) (hL := hL) (S := S) ∧
        ∃ q : FinitePath Gamma.graph,
          q.start ∈ Gamma.source ∧ q.finish = b ∧
            q.IsPrefixOf D.ownerPrefix ∧
            q.edgeSet ⊆ D.ownerPrefix.edgeSet) ∨
      (b ∈ reservedStrongSelectedSourceFirstBB
          (L := L) (hL := hL) (S := S) ∧
        GroundingCut.Before D.owner D.contact.vertex b ∧
        ∃ (q tail : FinitePath Gamma.graph),
          q.start ∈ Gamma.source ∧ q.finish = b ∧
            q.support ⊆ D.owner.support ∧
            q.edgeSet ⊆ D.owner.edgeSet ∧
            D.ownerPrefix.walk.length < q.walk.length ∧
            tail.start = D.contact.vertex ∧ tail.finish = b ∧
            tail.edgeSet ⊆ D.owner.edgeSet) := by
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix D.owner hbOwner
  have hqSource : q.start ∈ Gamma.source := hqStart ▸ D.owner_source
  have hcontact : D.contact.vertex ∈ D.owner.support := D.contact_mem_owner
  have retained_of_before
      (hbefore : GroundingCut.BeforeEq D.owner b D.contact.vertex) :
      b ∈ reservedStrongSelectedSourceFirstBB
            (L := L) (hL := hL) (S := S) ∧
        ∃ q : FinitePath Gamma.graph,
          q.start ∈ Gamma.source ∧ q.finish = b ∧
            q.IsPrefixOf D.ownerPrefix ∧
            q.edgeSet ⊆ D.ownerPrefix.edgeSet := by
    have hfinishBefore : GroundingCut.BeforeEq D.owner
        q.finish D.ownerPrefix.finish := by
      simpa only [hqFinish, D.prefix_finish] using hbefore
    have hlen : q.walk.length ≤ D.ownerPrefix.walk.length :=
      initialSubpath_length_le_of_beforeEq_finish D.owner
        q D.ownerPrefix hqStart D.prefix_start hqEdges D.prefix_edges
          hfinishBefore
    have hprefix : q.IsPrefixOf D.ownerPrefix :=
      initialSubpath_isPrefixOf_of_length_le D.owner
        q D.ownerPrefix hqStart D.prefix_start hqEdges D.prefix_edges hlen
    have hedge : q.edgeSet ⊆ D.ownerPrefix.edgeSet :=
      q.walk.edgeSet_subset_of_support_prefix D.ownerPrefix.walk hprefix
    exact ⟨hb, q, hqSource, hqFinish, hprefix, hedge⟩
  rcases GroundingCut.beforeEq_total hbOwner hcontact with hbefore | hafter
  · exact Or.inl (retained_of_before hbefore)
  · by_cases heq : D.contact.vertex = b
    · apply Or.inl
      apply retained_of_before
      rw [← heq]
      exact GroundingCut.beforeEq_refl hcontact
    · right
      have hstrict : GroundingCut.Before D.owner D.contact.vertex b :=
        ⟨hafter, heq⟩
      have hfinishStrict : GroundingCut.Before D.owner
          D.ownerPrefix.finish q.finish := by
        simpa only [D.prefix_finish, hqFinish] using hstrict
      have hlen : D.ownerPrefix.walk.length < q.walk.length :=
        initialSubpath_length_lt_of_before_finish D.owner
          D.ownerPrefix q D.prefix_start hqStart D.prefix_edges hqEdges
            hfinishStrict
      obtain ⟨tail, htailStart, htailFinish, htailEdges⟩ :=
        GroundingCutDecoder.exists_forward_segment_of_before hstrict
      exact ⟨hb, hstrict, q, tail, hqSource, hqFinish, hqSupport,
        hqEdges, hlen, htailStart, htailFinish, htailEdges⟩

/-- Every edge of an initial prefix retained by source saturation survives
the literal saturated switch.  Indeed the normalized suffix has no return
to any source-grounded owner away from the splice contact, so it cannot use
a nontrivial edge of the retained prefix in either direction. -/
theorem retainedPrefix_edgeSet_subset_switchedEdges
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q)
    (q : FinitePath Gamma.graph) (hq : q.IsPrefixOf D.ownerPrefix) :
    q.edgeSet ⊆ switchedEdges D.saturatedWarp (.finite Q) := by
  intro e he
  have hePrefix : e ∈ D.ownerPrefix.edgeSet :=
    q.walk.edgeSet_subset_of_support_prefix D.ownerPrefix.walk hq he
  have heFamily : e ∈ Alternating.familyEdges D.saturatedWarp := by
    simp only [Alternating.familyEdges, Set.mem_iUnion]
    exact ⟨(.inl D.ownerPrefix : Gamma.DPath), Set.mem_insert _ _, hePrefix⟩
  have hnotQ : e ∉ (AltPath.finite Q).edgeSet := by
    intro heQ
    have heQEnds := (AltPath.finite Q).edgeSet_subset_vertexSet_prod heQ
    have htailSuffix : e.1 ∈ D.normalizedSuffix.path.vertexSet := by
      rw [hQ]
      exact heQEnds.1
    have hheadSuffix : e.2 ∈ D.normalizedSuffix.path.vertexSet := by
      rw [hQ]
      exact heQEnds.2
    have heEnds := q.edgeSet_subset_support_prod he
    have hqSupport : q.support ⊆ D.ownerPrefix.support := hq.support_subset
    have htailCarrier : e.1 ∈ X.sourceGroundedCarrier :=
      ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩,
        D.prefix_support (hqSupport heEnds.1)⟩
    have hheadCarrier : e.2 ∈ X.sourceGroundedCarrier :=
      ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩,
        D.prefix_support (hqSupport heEnds.2)⟩
    have htail :=
      D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
        htailSuffix htailCarrier
    have hhead :=
      D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
        hheadSuffix hheadCarrier
    exact (path_edge_ne_of_mem (.inl q : Gamma.DPath) he)
      (htail.trans hhead.symm)
  exact Or.inl ⟨heFamily, hnotQ⟩

/-- Relation-facing source-first accounting.  A required point on the
sacrificed source-grounded owner is either already rooted in the literal
saturated switch through the retained prefix, or is the named strictly
later owner obligation carrying a finite tail and a strict length measure.
This is the one-step non-cycling datum for the simultaneous sink trade. -/
theorem sourceFirstBoundary_rooted_or_strictOwnerTail
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q) {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hbOwner : b ∈ D.owner.support) :
    (∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            switchedEdges D.saturatedWarp (.finite Q)) a b) ∨
      (b ∈ reservedStrongSelectedSourceFirstBB
          (L := L) (hL := hL) (S := S) ∧
        GroundingCut.Before D.owner D.contact.vertex b ∧
        ∃ (q tail : FinitePath Gamma.graph),
          q.start ∈ Gamma.source ∧ q.finish = b ∧
            q.support ⊆ D.owner.support ∧
            q.edgeSet ⊆ D.owner.edgeSet ∧
            D.ownerPrefix.walk.length < q.walk.length ∧
            tail.start = D.contact.vertex ∧ tail.finish = b ∧
            tail.edgeSet ⊆ D.owner.edgeSet) := by
  rcases D.sourceFirstBoundary_retainedPrefix_or_strictOwnerTail
      hb hbOwner with hretained | hstrict
  · obtain ⟨_hb, q, hqSource, hqFinish, hqPrefix, _hqEdges⟩ := hretained
    left
    refine ⟨q.start, hqSource, ?_⟩
    have hwalk := Alternating.Walk.reflTransGen_edgeSet q.walk
    have hedge := D.retainedPrefix_edgeSet_subset_switchedEdges Q hQ q hqPrefix
    simpa only [hqFinish] using
      Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ q.edgeSet)
        (p := fun x y ↦ (x, y) ∈
          switchedEdges D.saturatedWarp (.finite Q))
        (fun _ _ he ↦ hedge he) q.start q.finish hwalk
  · exact Or.inr hstrict

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.sourceFirstBoundary_retainedPrefix_or_strictOwnerTail
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.sourceFirstBoundary_rooted_or_strictOwnerTail
