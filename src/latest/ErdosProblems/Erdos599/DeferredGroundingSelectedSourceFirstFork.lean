/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstTransfer

/-!
# The literal fork at a saturated source-owner contact

After source-owner saturation, the remaining selected suffix has no further
contact with a source-grounded owner.  If a required source-first point lies
strictly after the saturation contact, restoring the old owner and following
the selected request are therefore compatible everywhere except at the one
outgoing incidence of the saturation contact.

This file records that statement with the actual finite owner prefix and the
actual first selected link.  In particular, it does not choose one branch or
postulate a simultaneous matching between different owners.
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

/-- A vertex of an initial finite subpath which occurs no later than its
endpoint on the reference path really belongs to that finite subpath. -/
theorem initialSubpath_mem_of_beforeEq_finish
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hqStart : q.start = P.initial)
    (hqEdges : q.edgeSet ⊆ P.edgeSet)
    {x : V} (hbefore : GroundingCut.BeforeEq P x q.finish) :
    x ∈ q.support := by
  obtain ⟨m, n, hmx, hnq, hmn⟩ := hbefore
  have hxP : x ∈ P.support := GroundingCut.occursAt_mem_support hmx
  obtain ⟨p, hpStart, hpFinish, _hpSupport, hpEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix P hxP
  have hfinishBefore : GroundingCut.BeforeEq P p.finish q.finish := by
    exact ⟨m, n, hpFinish ▸ hmx, hnq, hmn⟩
  have hlength : p.walk.length ≤ q.walk.length :=
    initialSubpath_length_le_of_beforeEq_finish P p q
      hpStart hqStart hpEdges hqEdges hfinishBefore
  have hpq : p.IsPrefixOf q :=
    initialSubpath_isPrefixOf_of_length_le P p q
      hpStart hqStart hpEdges hqEdges hlength
  exact hpq.support_subset (hpFinish ▸ p.finish_mem_support)

/-- The saturation contact lies on the longer source prefix which restores
the final required point of the sacrificed owner. -/
theorem LastSourceFirstPrefix.contact_mem_sourcePrefix
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    D.contact.vertex ∈ F.sourcePrefix.support := by
  apply initialSubpath_mem_of_beforeEq_finish D.owner F.sourcePrefix
    F.sourcePrefix_start F.sourcePrefix_edges
  simpa only [F.sourcePrefix_finish] using F.contact_before.1

/-- The selected suffix and the restored owner prefix meet at exactly the
saturation contact.  This is the carrier form of the one-incidence fork. -/
theorem LastSourceFirstPrefix.normalizedSuffix_inter_sourcePrefix
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    D.normalizedSuffix.path.vertexSet ∩ F.sourcePrefix.support =
      {D.contact.vertex} := by
  apply Set.Subset.antisymm
  · intro v hv
    have hvCarrier : v ∈ X.sourceGroundedCarrier :=
      ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩,
        F.sourcePrefix_support hv.2⟩
    exact Set.mem_singleton_iff.2
      (D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
        hv.1 hvCarrier)
  · intro v hv
    have hvEq : v = D.contact.vertex := Set.mem_singleton_iff.1 hv
    subst v
    refine ⟨?_, F.contact_mem_sourcePrefix⟩
    simpa only [D.normalizedSuffix_initial] using
      D.normalizedSuffix.path.initial_mem_vertexSet

/-- A nontrivial finite saturated suffix must leave the saturation contact
forwards.  A backward first link would lie on the newly retained grounded
owner prefix, but the last-contact property says that the suffix meets that
whole grounded carrier only at the contact. -/
theorem finiteSuffix_firstLink_forward
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q) :
    Q.firstLink.direction = .forward := by
  cases hdir : Q.firstLink.direction with
  | forward => rfl
  | backward =>
      have hback := D.normalizedSuffix_backwardLinksOn_saturatedWarp
      rw [hQ] at hback
      obtain ⟨Y, hY, hlinkY⟩ :=
        hback Q.firstLink Q.firstLink_mem_links hdir
      have hQInitial : Q.initial = D.contact.vertex := by
        have h := D.normalizedSuffix_initial
        rw [hQ] at h
        simpa only [AltPath.initial] using h
      have hcontactY : D.contact.vertex ∈ Y.support := by
        rw [← hQInitial]
        change Q.firstLink.entry ∈ Y.support
        rw [Link.entry, hdir]
        exact hlinkY.1 Q.firstLink.path.finish_mem_support
      have hcontactPrefix : D.contact.vertex ∈
          DirectedPath.Path.support
            (Sum.inl D.ownerPrefix : Gamma.DPath) := by
        change D.contact.vertex ∈ D.ownerPrefix.support
        rw [← D.prefix_finish]
        exact D.ownerPrefix.finish_mem_support
      have hprefixMem : (Sum.inl D.ownerPrefix : Gamma.DPath) ∈
          D.saturatedWarp := Set.mem_insert _ _
      have hYEq : Y = (Sum.inl D.ownerPrefix : Gamma.DPath) :=
        DWeb.IsWarp.eq_of_mem_support D.saturatedWarp_isWarp hY hprefixMem
          hcontactY hcontactPrefix
      have hexitSuffix : Q.firstLink.exit ∈
          D.normalizedSuffix.path.vertexSet := by
        rw [hQ]
        exact (AltPath.finite Q).link_support_subset_vertexSet
          Q.firstLink_mem_links Q.firstLink.exit_mem_support
      have hexitCarrier : Q.firstLink.exit ∈ X.sourceGroundedCarrier := by
        refine ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩, ?_⟩
        apply D.prefix_support
        have hexitY : Q.firstLink.exit ∈ Y.support :=
          hlinkY.1 Q.firstLink.exit_mem_support
        simpa only [hYEq, Path.support] using hexitY
      have hexitEq :=
        D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
          hexitSuffix hexitCarrier
      exfalso
      apply Q.firstLink.nontrivial
      have hentry : Q.firstLink.entry = D.contact.vertex := hQInitial
      have hexit : Q.firstLink.exit = D.contact.vertex := hexitEq
      simpa only [Link.entry, Link.exit, hdir] using
        (hentry.trans hexit.symm).symm

/-- The exact competing outgoing incidence.  The old-owner restoration and
the selected request agree only at the saturation contact, and their first
edges there are distinct: the restoration edge is an edge of the sacrificed
owner, while the selected edge is not an edge of any source-grounded owner.

This is the finite local datum which a global alternating matching must
resolve. -/
theorem LastSourceFirstPrefix.exists_competing_outgoing_of_finiteSuffix
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q) :
    ∃ y z : V,
      (D.contact.vertex, y) ∈ F.sourcePrefix.edgeSet ∧
        (D.contact.vertex, z) ∈ Q.firstLink.path.edgeSet ∧
        Q.firstLink.direction = .forward ∧ y ≠ z ∧
        (D.contact.vertex, y) ∈ D.owner.edgeSet ∧
        (D.contact.vertex, z) ∉ D.owner.edgeSet := by
  have hcontactNeFinish :
      D.contact.vertex ≠ F.sourcePrefix.finish := by
    rw [F.sourcePrefix_finish]
    exact F.contact_before.2
  obtain ⟨y, hy⟩ :=
    FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      F.sourcePrefix F.contact_mem_sourcePrefix hcontactNeFinish
  have hfirst : Q.firstLink.direction = .forward :=
    D.finiteSuffix_firstLink_forward Q hQ
  have hQInitial : Q.initial = D.contact.vertex := by
    have h := D.normalizedSuffix_initial
    rw [hQ] at h
    simpa only [AltPath.initial] using h
  have hfirstStart : Q.firstLink.path.start = D.contact.vertex := by
    calc
      Q.firstLink.path.start = Q.firstLink.entry := by
        simp only [Link.entry, hfirst]
      _ = Q.initial := rfl
      _ = D.contact.vertex := hQInitial
  have hfirstNe : Q.firstLink.path.start ≠ Q.firstLink.path.finish := by
    intro heq
    apply Q.firstLink.nontrivial
    simpa only [Link.entry, Link.exit, hfirst] using heq
  obtain ⟨z, hz'⟩ :=
    FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      Q.firstLink.path Q.firstLink.path.start_mem_support hfirstNe
  have hz : (D.contact.vertex, z) ∈ Q.firstLink.path.edgeSet := by
    simpa only [hfirstStart] using hz'
  have hyOwner : (D.contact.vertex, y) ∈ D.owner.edgeSet :=
    F.sourcePrefix_edges hy
  have hzNotOwner : (D.contact.vertex, z) ∉ D.owner.edgeSet := by
    intro hzOwner
    have hzFamily : (D.contact.vertex, z) ∈
        Alternating.familyEdges X.sourceGroundedOwners := by
      simp only [Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩, hzOwner⟩
    exact Set.disjoint_left.mp
      (D.forwardLinksOff_sourceGroundedOwners Q.firstLink
        (by rw [hQ]; exact Q.firstLink_mem_links) hfirst) hz hzFamily
  refine ⟨y, z, hy, hz, hfirst, ?_, hyOwner, hzNotOwner⟩
  intro hyz
  subst z
  exact hzNotOwner hyOwner

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.normalizedSuffix_inter_sourcePrefix
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.finiteSuffix_firstLink_forward
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.exists_competing_outgoing_of_finiteSuffix
