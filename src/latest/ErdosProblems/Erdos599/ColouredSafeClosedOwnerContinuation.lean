/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafePostClosureEndpointExposure
import ErdosProblems.Erdos599.LadderConstantLimit
import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# Real continuations on covered limiting-reference owners

Whole-reference closure gives more than a set-theoretic obstruction at a
covered endpoint.  A limiting owner contained in the native closed set has
the following exact later-stage behavior.

* If it meets the captured frontier, roof confinement makes it equal to its
  finite essential stage prefix.  It therefore ends at that frontier, and
  stable capture makes the endpoint persistent.
* If it misses the frontier, it is literally an inessential member of the
  later stage warp.  Such a member need not be finite.

Consequently every covered vertex has a genuine directed continuation in
the original graph, namely the suffix of its whole limiting owner.  In the
frontier-hit case this is a finite path to a persistent vertex; otherwise
its owner is one of the already absorbed inessential components.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {R : LimitClosure C seed}

namespace ClosedLimitOwner

/-- The genuinely inessential alternative at the chosen club stage has
small carrier.  This bounds the ray/strict-roof exception; it does not turn
its members into finite paths. -/
theorem mk_inessentialCarrier_later_le
    (R : LimitClosure C seed) :
    #(C.inessentialCarrierAt R.later.stage) ≤ kappa := by
  apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
    C.legal C.capacity_infinite R.later.stage
  exact fun hphi ↦ Set.disjoint_left.mp C.club_avoids_phi
    R.later.mem_club hphi

/-- Suffix continuations carried by distinct limiting owners are disjoint.
Thus global collision control reduces exactly to choosing at most one
continuation per limiting owner. -/
theorem disjoint_suffixes_of_distinct_owners
    {p q : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    (hq : q ∈ C.ladder.limitWarp) (hpq : p ≠ q)
    {x y : V} (hxp : x ∈ p.support) (hyq : y ∈ q.support) :
    Disjoint (p.suffixFrom x hxp).support
      (q.suffixFrom y hyq).support :=
  (C.legal.warpStages (Ladder.finalStage (succ kappa)) hp hq hpq).mono
    (Path.support_suffixFrom_subset p x hxp)
    (Path.support_suffixFrom_subset q y hyq)

/-- A whole closed limiting owner which meets the captured frontier is
itself finite and ends at the (persistent) point of contact. -/
theorem finite_persistent_owner_of_frontier_hit
    (R : LimitClosure C seed) {p : Gamma.DPath}
    (hp : p ∈ C.ladder.limitWarp)
    (hpClosed : p.support ⊆ R.closedSet)
    {v : V} (hvp : v ∈ p.support)
    (hvFrontier : v ∈ C.ladder.frontier R.later.stage) :
    ∃ f : FinitePath Gamma.graph,
      p = .inl f ∧ f.finish = v ∧ f.support ⊆ R.closedSet ∧
        v ∈ C.persistent := by
  obtain ⟨q, hq, hqTerminal, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp hvFrontier hvp
  obtain ⟨f, rfl⟩ := ladderReference.finiteCharacter hq
  have hpRoof : p.support ⊆
      Gamma.roof (C.ladder.frontier R.later.stage) :=
    hpClosed.trans R.later.subset_roof
  have hpSubset : p.support ⊆
      Path.support (Sum.inl f : Gamma.DPath) := by
    intro x hxp
    exact DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      C.legal R.later.stage hp hq.1 hqp ⟨hxp, hpRoof hxp⟩
  have heq : (Sum.inl f : Gamma.DPath) = p :=
    Path.eq_of_extends_of_support_subset hqp hpSubset
  have hfinish : f.finish = v := Option.some.inj hqTerminal
  have hvClosed : v ∈ R.closedSet := hpClosed hvp
  have hvPersistent : v ∈ C.persistent := by
    have hpair : v ∈ R.closedSet ∩ C.ladder.frontier R.later.stage :=
      ⟨hvClosed, hvFrontier⟩
    rw [R.frontier_inter] at hpair
    exact hpair.2
  have hfClosed : f.support ⊆ R.closedSet := by
    have hpClosed' := hpClosed
    rw [← heq] at hpClosed'
    exact hpClosed'
  exact ⟨f, heq.symm, hfinish, hfClosed, hvPersistent⟩

/-- A whole closed limiting owner either is a finite path to the persistent
frontier, or is literally an inessential later-stage component. -/
theorem finite_persistent_owner_or_inessential
    (R : LimitClosure C seed) {p : Gamma.DPath}
    (hp : p ∈ C.ladder.limitWarp)
    (hpClosed : p.support ⊆ R.closedSet) :
    (∃ f : FinitePath Gamma.graph,
      p = .inl f ∧ f.finish ∈ C.persistent ∧
        f.support ⊆ R.closedSet) ∨
      p ∈ Gamma.inessentialPaths (C.ladder.warpAt R.later.stage) := by
  by_cases hhit : p ∈ C.limitReferenceAtFrontier R.later.stage
  · obtain ⟨v, hvp, hvFrontier⟩ := hhit.2
    obtain ⟨f, hpf, hfinish, hfClosed, hvPersistent⟩ :=
      finite_persistent_owner_of_frontier_hit R hp hpClosed hvp hvFrontier
    exact Or.inl ⟨f, hpf, hfinish ▸ hvPersistent, hfClosed⟩
  · right
    have hpInitialClosed : p.initial ∈ R.closedSet :=
      hpClosed p.initial_mem_support
    have hpInitialRoof : p.initial ∈
        Gamma.roof (C.ladder.frontier R.later.stage) :=
      R.later.subset_roof hpInitialClosed
    exact C.mem_inessentialPaths_of_roofedLimitReferenceMiss
      R.later.stage ⟨hp, hpInitialRoof, hhit⟩

/-- Positive covered-source replacement.  From any point on a whole closed
owner, take its literal directed suffix.  The suffix stays in the closed
set and either is finite with persistent terminal, or belongs to an owner
which is inessential at the captured stage. -/
theorem exists_forwardContinuation_of_closed_limitOwner
    (R : LimitClosure C seed) {w : V}
    (hwClosed : w ∈ R.closedSet)
    (hwGlobal : w ∈ Gamma.vertexSet C.ladder.limitWarp) :
    ∃ p ∈ C.ladder.limitWarp, ∃ hw : w ∈ p.support,
      p.support ⊆ R.closedSet ∧
      let q := p.suffixFrom w hw
      q.initial = w ∧ q.support ⊆ R.closedSet ∧
        ((∃ f : FinitePath Gamma.graph,
            q = .inl f ∧ f.finish ∈ C.persistent) ∨
          p ∈ Gamma.inessentialPaths
            (C.ladder.warpAt R.later.stage)) := by
  obtain ⟨p, hp, hwp, hpClosed⟩ :=
    NativePostClosureIntervalTransaction.exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex
      R hwClosed hwGlobal
  refine ⟨p, hp, hwp, hpClosed, ?_, ?_, ?_⟩
  · rcases p with f | r
    · exact f.suffixFromAux_start w hwp
    · exact r.initial_suffixFrom w hwp
  · exact (Path.support_suffixFrom_subset p w hwp).trans hpClosed
  · rcases finite_persistent_owner_or_inessential R hp hpClosed with
      ⟨f, hpf, hfPersistent, _hfClosed⟩ | hpInessential
    · left
      subst p
      change w ∈ f.support at hwp
      exact ⟨f.suffixFromAux w hwp, rfl, by
        exact f.suffixFromAux_finish w hwp ▸ hfPersistent⟩
    · exact Or.inr hpInessential

/-- Actual endpoint replacement for a finite path which reaches the closed
set at a limiting-reference vertex.  If the starting vertex is not on the
limiting reference and the old path meets the closed set only at its two
displayed endpoints, its terminal-owner suffix can be concatenated
literally.  Thus this operation preserves the old source; it does not drop
the covered hole.  The resulting real path either finishes persistently or
continues on a later-stage inessential owner (which may be a ray). -/
theorem exists_appendedForwardContinuation_of_closed_terminal
    (R : LimitClosure C seed) (q : FinitePath Gamma.graph)
    (hqStartOff : q.start ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hqClosed : q.finish ∈ R.closedSet)
    (hqGlobal : q.finish ∈ Gamma.vertexSet C.ladder.limitWarp)
    (hqCut : q.support ∩ R.closedSet ⊆ {q.start, q.finish}) :
    ∃ (p : Gamma.DPath) (hp : p ∈ C.ladder.limitWarp)
        (ht : q.finish ∈ p.support) (hpClosed : p.support ⊆ R.closedSet),
      let tail := p.suffixFrom q.finish ht
      ∃ (htailStart : tail.initial = q.finish)
          (hinter : q.support ∩ tail.support ⊆ {q.finish}),
      let out := Path.appendFinite q tail htailStart hinter
      out.initial = q.start ∧
        out.support = q.support ∪ tail.support ∧
        ((∃ f : FinitePath Gamma.graph,
            out = .inl f ∧ f.finish ∈ C.persistent) ∨
          p ∈ Gamma.inessentialPaths
            (C.ladder.warpAt R.later.stage)) := by
  obtain ⟨p, hp, htp, hpClosed⟩ :=
    NativePostClosureIntervalTransaction.exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex
      R hqClosed hqGlobal
  let tail := p.suffixFrom q.finish htp
  have htailStart : tail.initial = q.finish := by
    rcases p with f | r
    · exact f.suffixFromAux_start q.finish htp
    · exact r.initial_suffixFrom q.finish htp
  have hinter : q.support ∩ tail.support ⊆ {q.finish} := by
    rintro x ⟨hxq, hxtail⟩
    have hxp : x ∈ p.support :=
      Path.support_suffixFrom_subset p q.finish htp hxtail
    have hxClosed : x ∈ R.closedSet := hpClosed hxp
    rcases hqCut ⟨hxq, hxClosed⟩ with hxs | hxt
    · exact False.elim (hqStartOff (hxs ▸ ⟨p, hp, hxp⟩))
    · exact hxt
  let out := Path.appendFinite q tail htailStart hinter
  refine ⟨p, hp, htp, hpClosed, htailStart, hinter, ?_, ?_, ?_⟩
  · exact Path.initial_appendFinite q tail htailStart hinter
  · exact Path.support_appendFinite q tail htailStart hinter
  · rcases finite_persistent_owner_or_inessential R hp hpClosed with
      ⟨f, hpf, hfPersistent, _hfClosed⟩ | hpInessential
    · left
      subst p
      change q.finish ∈ f.support at htp
      let g := q.appendFinite (f.suffixFromAux q.finish htp)
        htailStart hinter
      refine ⟨g, ?_, ?_⟩
      · rfl
      · change g.finish ∈ C.persistent
        rw [show g.finish = f.finish from
          q.appendFinite_finish (f.suffixFromAux q.finish htp)
            htailStart hinter]
        exact hfPersistent
    · exact Or.inr hpInessential
#print axioms ClosedLimitOwner.finite_persistent_owner_of_frontier_hit
#print axioms ClosedLimitOwner.mk_inessentialCarrier_later_le
#print axioms ClosedLimitOwner.disjoint_suffixes_of_distinct_owners
#print axioms ClosedLimitOwner.finite_persistent_owner_or_inessential
#print axioms ClosedLimitOwner.exists_forwardContinuation_of_closed_limitOwner
#print axioms
  ClosedLimitOwner.exists_appendedForwardContinuation_of_closed_terminal

end ClosedLimitOwner
end Erdos599.Blueprint.LinkageBlueprint
