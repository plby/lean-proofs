/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceSafeStep
import ErdosProblems.Erdos599.ColouredSafeReferenceIntervalChoice

/-!
# Full-interval anchored backward choices

The reverse-reachability recursion chooses the first reference point outside
a dynamically defined set.  Normalizing a *fixed* finite safe word needs a
different anchor: the lower endpoint of the full interval removed by that
word on the reference owner.  This file constructs that choice directly.

No continuation or normalization result is assumed.  The output is the
literal fresh subpath from the old upper endpoint to the new contact, and all
of its edges are proved to belong to the fixed total removed relation.
-/

noncomputable section

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A concrete finite representative of a nonempty full removed interval on
one finite reference owner. -/
structure FullRemovedInterval (owner : FinitePath Gamma.graph)
    (R : Set (V × V)) where
  path : FinitePath Gamma.graph
  isSubpath : path.IsSubpathOf (.inl owner)
  removed_eq : R ∩ owner.edgeSet = path.edgeSet

/-- A nonempty abstract edge interval on a finite owner has a concrete finite
representative.  The supplied edge rules out the empty alternative. -/
theorem exists_fullRemovedInterval_of_mem
    {owner : FinitePath Gamma.graph} {R : Set (V × V)}
    (hinterval : IsEdgeInterval (R ∩ owner.edgeSet) (.inl owner))
    {e : V × V} (he : e ∈ R ∩ owner.edgeSet) :
    Nonempty (FullRemovedInterval owner R) := by
  rcases hinterval with hempty | ⟨q, hq, hEq⟩
  · exact False.elim (by simpa [hempty] using he)
  · obtain ⟨p, rfl⟩ := Path.finite_of_isSubpathOf_finite hq
    exact ⟨⟨p, hq, hEq⟩⟩

/-- A prefix interval already selected by the normalization.  Its lower
endpoint is the lower endpoint of the fixed full interval. -/
structure FullAnchoredPriorInterval
    (owner : FinitePath Gamma.graph)
    (Rtotal Rprefix Fprefix : Set (V × V)) where
  full : FinitePath Gamma.graph
  prior : FinitePath Gamma.graph
  full_isSubpath : full.IsSubpathOf (.inl owner)
  prior_isSubpath_full : prior.IsSubpathOf (.inl full)
  total_removed_eq : Rtotal ∩ owner.edgeSet = full.edgeSet
  prefix_removed_eq : Rprefix ∩ owner.edgeSet = prior.edgeSet
  same_start : prior.start = full.start
  finish_incoming : HasIncoming Fprefix prior.finish

/-- The backward interval selected at the next contact.  `old` is trivial
on a first visit and is the old anchored prefix on a revisit. -/
structure FullAnchoredBackwardChoice
    (owner : FinitePath Gamma.graph)
    (Rtotal Rprefix : Set (V × V)) (w : V) where
  full : FinitePath Gamma.graph
  old : FinitePath Gamma.graph
  extension : FinitePath Gamma.graph
  full_isSubpath : full.IsSubpathOf (.inl owner)
  old_isSubpath_full : old.IsSubpathOf (.inl full)
  extension_isSubpath_full : extension.IsSubpathOf (.inl full)
  total_removed_eq : Rtotal ∩ owner.edgeSet = full.edgeSet
  prefix_removed_eq : Rprefix ∩ owner.edgeSet = old.edgeSet
  same_start : old.start = full.start
  join : old.finish = extension.start
  extension_finish : extension.finish = w
  extension_nontrivial : extension.start ≠ extension.finish
  extension_edges_total : extension.edgeSet ⊆ Rtotal
  fresh : Disjoint extension.edgeSet Rprefix

theorem FullAnchoredBackwardChoice.old_isSubpath_owner
    {owner : FinitePath Gamma.graph}
    {Rtotal Rprefix : Set (V × V)} {w : V}
    (K : FullAnchoredBackwardChoice owner Rtotal Rprefix w) :
    K.old.IsSubpathOf (.inl owner) :=
  ⟨K.old_isSubpath_full.1.trans K.full_isSubpath.1,
    K.old_isSubpath_full.2.trans K.full_isSubpath.2⟩

theorem FullAnchoredBackwardChoice.extension_isSubpath_owner
    {owner : FinitePath Gamma.graph}
    {Rtotal Rprefix : Set (V × V)} {w : V}
    (K : FullAnchoredBackwardChoice owner Rtotal Rprefix w) :
    K.extension.IsSubpathOf (.inl owner) :=
  ⟨K.extension_isSubpath_full.1.trans K.full_isSubpath.1,
    K.extension_isSubpath_full.2.trans K.full_isSubpath.2⟩

private theorem full_start_before_head_of_edge
    {p : FinitePath Gamma.graph} {y w : V} (hyw : (y, w) ∈ p.edgeSet) :
    GroundingCut.Before (.inl p : Gamma.DPath) p.start w := by
  have hw : w ∈ p.support := (p.edgeSet_subset_support_prod hyw).2
  have hne : p.start ≠ w := by
    intro h
    exact FinitePath.no_incoming_edge_at_start p y (h ▸ hyw)
  obtain h | h := p.orderedOccurrence_or_reverse p.start_mem_support hw hne
  · exact PathOrder.before_of_orderedOccurrence h.some
  · obtain ⟨hrev⟩ := h
    let q := p.between hrev
    obtain ⟨z, hz⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start q
      q.finish_mem_support hrev.ne.symm
    have hz' : (z, p.start) ∈ p.edgeSet := by
      simpa [q] using p.between_edgeSet_subset hrev hz
    exact False.elim (FinitePath.no_incoming_edge_at_start p z hz')

private theorem exists_choice_of_empty
    {owner : FinitePath Gamma.graph} {Rtotal Rprefix : Set (V × V)}
    (full : FullRemovedInterval owner Rtotal)
    {y w : V} (hyw : (y, w) ∈ Rtotal ∩ owner.edgeSet)
    (hempty : Rprefix ∩ owner.edgeSet = ∅) :
    Nonempty (FullAnchoredBackwardChoice owner Rtotal Rprefix w) := by
  have hywFull : (y, w) ∈ full.path.edgeSet := by
    rw [← full.removed_eq]
    exact hyw
  have hbefore := full_start_before_head_of_edge hywFull
  obtain ⟨hocc⟩ := PathOrder.orderedOccurrence_of_before hbefore
  let old := FinitePath.trivial Gamma.graph full.path.start
  let extension := full.path.between hocc
  have hold : old.IsSubpathOf (.inl full.path) := by
    constructor
    · intro x hx
      have hx' : x = full.path.start := by
        change x ∈ (FinitePath.trivial Gamma.graph full.path.start).support at hx
        simpa only [FinitePath.support_trivial, Set.mem_singleton_iff] using hx
      exact hx' ▸ full.path.start_mem_support
    · simp [old, FinitePath.edgeSet, FinitePath.trivial]
  have hext : extension.IsSubpathOf (.inl full.path) :=
    full.path.between_isSubpathOf hocc
  have holdEq : Rprefix ∩ owner.edgeSet = old.edgeSet := by
    rw [hempty]
    simp [old, FinitePath.edgeSet, FinitePath.trivial]
  have hfresh : Disjoint extension.edgeSet Rprefix := by
    apply Set.disjoint_left.2
    intro e hextE heR
    have heOwner : e ∈ owner.edgeSet :=
      full.isSubpath.2 (hext.2 hextE)
    have : e ∈ old.edgeSet := by
      rw [← holdEq]
      exact ⟨heR, heOwner⟩
    simpa [old, FinitePath.edgeSet, FinitePath.trivial] using this
  exact ⟨{
    full := full.path
    old := old
    extension := extension
    full_isSubpath := full.isSubpath
    old_isSubpath_full := hold
    extension_isSubpath_full := hext
    total_removed_eq := full.removed_eq
    prefix_removed_eq := holdEq
    same_start := rfl
    join := by simp [old, extension]
    extension_finish := by simp [extension]
    extension_nontrivial := by simpa [extension] using hbefore.2
    extension_edges_total := fun e he ↦ by
      have heFull := hext.2 he
      have he' : e ∈ Rtotal ∩ owner.edgeSet := by
        rw [full.removed_eq]
        exact heFull
      exact he'.1
    fresh := hfresh }⟩

private theorem exists_choice_of_prior
    {owner : FinitePath Gamma.graph}
    {Rtotal Rprefix Fprefix : Set (V × V)}
    (A : FullAnchoredPriorInterval owner Rtotal Rprefix Fprefix)
    {y w : V} (hyw : (y, w) ∈ Rtotal ∩ owner.edgeSet)
    (hwInterior : w ∉ removedInterior Rprefix)
    (hwNoIncoming : ¬HasIncoming Fprefix w) :
    Nonempty (FullAnchoredBackwardChoice owner Rtotal Rprefix w) := by
  have hywFull : (y, w) ∈ A.full.edgeSet := by
    rw [← A.total_removed_eq]
    exact hyw
  have hstartW := full_start_before_head_of_edge hywFull
  have huFull : A.prior.finish ∈ A.full.support :=
    A.prior_isSubpath_full.1 A.prior.finish_mem_support
  have hwFull : w ∈ A.full.support :=
    (A.full.edgeSet_subset_support_prod hywFull).2
  have huwNe : A.prior.finish ≠ w := by
    intro h
    exact hwNoIncoming (h ▸ A.finish_incoming)
  have hnotReverse :
      ¬Nonempty (FinitePath.OrderedOccurrence A.full w A.prior.finish) := by
    rintro ⟨hrev⟩
    have hwPrior : w ∈ A.prior.support := by
      apply PathOrder.mem_support_of_between_subpath A.full A.prior
        A.prior_isSubpath_full hwFull
      · simpa only [A.same_start] using hstartW
      · exact PathOrder.before_of_orderedOccurrence hrev
    have hwStart : w ≠ A.prior.start := by
      intro h
      have : A.full.start = w := A.same_start.symm.trans h.symm
      exact hstartW.2 this
    have hwFinish : w ≠ A.prior.finish := huwNe.symm
    obtain ⟨a, ha⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        A.prior hwPrior hwStart
    obtain ⟨b, hb⟩ :=
      FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        A.prior hwPrior hwFinish
    apply hwInterior
    constructor
    · exact ⟨a, by
        have : (a, w) ∈ Rprefix ∩ owner.edgeSet := by
          rw [A.prefix_removed_eq]
          exact ha
        exact this.1⟩
    · exact ⟨b, by
        have : (w, b) ∈ Rprefix ∩ owner.edgeSet := by
          rw [A.prefix_removed_eq]
          exact hb
        exact this.1⟩
  obtain ⟨hocc⟩ := A.full.orderedOccurrence_of_not_reverse
    huFull hwFull huwNe hnotReverse
  let extension := A.full.between hocc
  have hext : extension.IsSubpathOf (.inl A.full) :=
    A.full.between_isSubpathOf hocc
  have hfresh : Disjoint extension.edgeSet Rprefix := by
    have hdisj := adjacent_subpaths_edgeSet_disjoint A.prior extension
      (.inl A.full : Gamma.DPath) A.prior_isSubpath_full hext (by simp [extension])
    apply Set.disjoint_left.2
    intro e hextE heR
    have heOwner : e ∈ owner.edgeSet :=
      A.full_isSubpath.2 (hext.2 hextE)
    have hePrior : e ∈ A.prior.edgeSet := by
      rw [← A.prefix_removed_eq]
      exact ⟨heR, heOwner⟩
    exact Set.disjoint_left.1 hdisj hePrior hextE
  exact ⟨{
    full := A.full
    old := A.prior
    extension := extension
    full_isSubpath := A.full_isSubpath
    old_isSubpath_full := A.prior_isSubpath_full
    extension_isSubpath_full := hext
    total_removed_eq := A.total_removed_eq
    prefix_removed_eq := A.prefix_removed_eq
    same_start := A.same_start
    join := by simp [extension]
    extension_finish := by simp [extension]
    extension_nontrivial := by simpa [extension] using hocc.ne
    extension_edges_total := fun e he ↦ by
      have heFull := hext.2 he
      have he' : e ∈ Rtotal ∩ owner.edgeSet := by
        rw [A.total_removed_eq]
        exact heFull
      exact he'.1
    fresh := hfresh }⟩

/-- Uniform fixed-word Rule-1/Rule-2 interval choice.  The first owner visit
uses the lower endpoint of the *full* removed interval; later visits extend
the already anchored prefix. -/
theorem exists_fullAnchoredBackwardChoice
    {owner : FinitePath Gamma.graph}
    {Rtotal Rprefix Fprefix : Set (V × V)}
    (hinterval : IsEdgeInterval (Rtotal ∩ owner.edgeSet) (.inl owner))
    (hprior : Rprefix ∩ owner.edgeSet = ∅ ∨
      Nonempty (FullAnchoredPriorInterval owner Rtotal Rprefix Fprefix))
    {y w : V} (hyw : (y, w) ∈ Rtotal ∩ owner.edgeSet)
    (hwInterior : w ∉ removedInterior Rprefix)
    (hwNoIncoming : ¬HasIncoming Fprefix w) :
    Nonempty (FullAnchoredBackwardChoice owner Rtotal Rprefix w) := by
  rcases hprior with hempty | hprior
  · obtain ⟨full⟩ := exists_fullRemovedInterval_of_mem hinterval hyw
    exact exists_choice_of_empty full hyw hempty
  · exact exists_choice_of_prior hprior.some hyw hwInterior hwNoIncoming

/-- After adding the chosen extension, its concatenation with the old prefix
is again anchored at the same full lower endpoint. -/
theorem FullAnchoredBackwardChoice.exists_updatedPrior
    {owner : FinitePath Gamma.graph}
    {Rtotal Rprefix Fnew : Set (V × V)} {w : V}
    (K : FullAnchoredBackwardChoice owner Rtotal Rprefix w)
    (hFin : HasIncoming Fnew w) :
    Nonempty (FullAnchoredPriorInterval owner Rtotal
      (Rprefix ∪ K.extension.edgeSet) Fnew) := by
  obtain ⟨p, hpStart, hpFinish, hpSub, _hpSupport, hpEdges⟩ :=
    FinitePath.exists_append_isSubpathOf K.old K.extension
      (.inl K.full : Gamma.DPath) K.old_isSubpath_full
      K.extension_isSubpath_full K.join
  refine ⟨{
    full := K.full
    prior := p
    full_isSubpath := K.full_isSubpath
    prior_isSubpath_full := hpSub
    total_removed_eq := K.total_removed_eq
    prefix_removed_eq := ?_
    same_start := hpStart.trans K.same_start
    finish_incoming := by simpa only [hpFinish, K.extension_finish] using hFin }⟩
  rw [Set.union_inter_distrib_right, K.prefix_removed_eq]
  have hextOwner : K.extension.edgeSet ⊆ owner.edgeSet :=
    K.extension_isSubpath_owner.2
  rw [Set.inter_eq_left.mpr hextOwner, hpEdges]

#print axioms exists_fullRemovedInterval_of_mem
#print axioms exists_fullAnchoredBackwardChoice
#print axioms FullAnchoredBackwardChoice.exists_updatedPrior

end Erdos599.Alternating.SwitchingCore.RelationalInterval
