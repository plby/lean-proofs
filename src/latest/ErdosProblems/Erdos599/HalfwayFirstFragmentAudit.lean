/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClosedEndpointPairing
import ErdosProblems.Erdos599.HalfwayCutFracturedProjection

/-!
# The first atomic fragment of a fractured assignment

The occurrence-split proof of Remark 4.20 begins every nontrivial selected
trace with one forward fragment of one literal hole.  This is useful local
geometry, but it is not yet the Claim-2 witness needed in Assertion 9.31.
If that fragment stops at a vertex of the reference warp, the one-link path
is not even alternating relative to the full reference warp: its last link
is forward and its terminal is covered.

The lemmas below isolate both statements.  In particular they prevent the
valid first-fragment observation from being silently promoted to a
`ClosedEndpointPairing` without the missing endpoint-selection/rerouting
argument.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {U Y : Set Gamma.DPath}
variable {W : Set Gamma.DPath} {X : Set V}

/-- Atomic fragments starting at the initials of two literal fractured
members cannot have the same exit unless they also have the same entry.

This is the precise injectivity available for first forward fragments.  If
their owners were distinct, the fractured-warp intersection condition would make
the common exit the initial vertex of one owner.  That fragment would then
have equal entry and exit, contrary to nontriviality. -/
theorem FracturedWarp.fragment_finish_injective_of_starts_at_initial
    (Z : FracturedWarp Gamma)
    {p q : Gamma.DPath} (hp : p ∈ Z.paths) (hq : q ∈ Z.paths)
    {P Q : FinitePath Gamma.graph}
    (hPsub : P.IsSubpathOf p) (hQsub : Q.IsSubpathOf q)
    (hPstart : P.start = p.initial) (hQstart : Q.start = q.initial)
    (hPne : P.start ≠ P.finish) (hQne : Q.start ≠ Q.finish)
    (hfinish : P.finish = Q.finish) :
    P.start = Q.start := by
  by_cases hpq : p = q
  · exact hPstart.trans ((congrArg Path.initial hpq).trans hQstart.symm)
  have hPfinishP : P.finish ∈ p.support :=
    hPsub.1 P.finish_mem_support
  have hPfinishQ : P.finish ∈ q.support := by
    apply hQsub.1
    rw [hfinish]
    exact Q.finish_mem_support
  have hmeet : ¬ Disjoint p.support q.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨P.finish, hPfinishP, hPfinishQ⟩
  rcases Z.allowed_intersection hp hq hpq hmeet with
    ⟨_hpNontrivial, _hqNontrivial, hcase | hcase⟩
  · rcases hcase with ⟨t, _hqterm, hpinitial, hinter⟩
    have hPt : P.finish = t := by
      have : P.finish ∈ p.support ∩ q.support :=
        ⟨hPfinishP, hPfinishQ⟩
      rw [hinter] at this
      simpa using this
    exact (hPne (hPstart.trans (hpinitial.trans hPt.symm))).elim
  · rcases hcase with ⟨t, _hpterm, hqinitial, hinter⟩
    have hQt : Q.finish = t := by
      have : Q.finish ∈ p.support ∩ q.support := by
        rw [← hfinish]
        exact ⟨hPfinishP, hPfinishQ⟩
      rw [hinter] at this
      simpa using this
    exact (hQne (hQstart.trans (hqinitial.trans hQt.symm))).elim

/-- A fragment which starts at the initial vertex of one concrete literal
outside hole meets the closing set only at the fragment's own endpoints.

The nontrivial point is the terminal of the owner: if it occurred internally
in the fragment, the fragment would have an outgoing owner edge there,
contradicting that it is the owner's finite terminal. -/
theorem OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.fragment_cut_vertex_is_endpoint
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    {p : Gamma.DPath} (hp : p ∈ F.outside.holes.paths)
    {P : FinitePath Gamma.graph} (hPsub : P.IsSubpathOf p)
    (hPstart : P.start = p.initial) {x : V}
    (hxP : x ∈ P.support) (hxX : x ∈ X) :
    P.start = x ∨ P.finish = x := by
  rcases F.cut_vertex_is_endpoint p hp (hPsub.1 hxP) hxX with
    hpInitial | hpTerminal
  · exact Or.inl (hPstart.trans hpInitial)
  · right
    by_contra hfinish
    obtain ⟨y, hxyP⟩ :=
      P.walk.exists_outgoing_edge_of_mem_of_ne_finish hxP
        (fun h => hfinish h.symm)
    have hxyOwner : (x, y) ∈ p.edgeSet := hPsub.2 hxyP
    rcases p with p | r
    · have hpFinish : p.finish = x := by
        simpa [DWeb.terminal?, Path.terminal?] using hpTerminal
      exact p.fst_ne_finish_of_mem_edge hxyOwner (hpFinish.symm)
    · simp [DWeb.terminal?, Path.terminal?] at hpTerminal

/-- A finite bracket-safe trace whose initial vertex is outside the
reference warp starts with a forward link. -/
theorem finite_firstLink_forward_of_bracketSafe
    {Q : FiniteTrace Gamma.graph}
    (hQ : IsBracketSafe U Y (.finite Q))
    (hinitial : Q.initial ∉ Gamma.vertexSet Y) :
    Q.firstLink.direction = .forward := by
  cases hdir : Q.firstLink.direction with
  | forward => rfl
  | backward =>
      have hfragment := hQ.isAlternating.2.1 Q.firstLink
        Q.firstLink_mem_links hdir
      rcases hfragment with ⟨p, hpY, hsub⟩
      apply (hinitial ⟨p, hpY, hsub.1 Q.firstLink.entry_mem_support⟩).elim

/-- The infinite version of `finite_firstLink_forward_of_bracketSafe`. -/
theorem infinite_firstLink_forward_of_bracketSafe
    {Q : InfiniteTrace Gamma.graph}
    (hQ : IsBracketSafe U Y (.infinite Q))
    (hinitial : Q.initial ∉ Gamma.vertexSet Y) :
    (Q.link 0).direction = .forward := by
  cases hdir : (Q.link 0).direction with
  | forward => rfl
  | backward =>
      have hfragment := hQ.isAlternating.2.1 (Q.link 0)
        Q.firstLink_mem_links hdir
      rcases hfragment with ⟨p, hpY, hsub⟩
      apply (hinitial ⟨p, hpY, hsub.1 (Q.link 0).entry_mem_support⟩).elim

/-- Consequently the first link of a finite bracket-safe trace is an
atomic fragment of the displayed forward family. -/
theorem finite_firstLink_isFragmentOf
    {Q : FiniteTrace Gamma.graph}
    (hQ : IsBracketSafe U Y (.finite Q))
    (hinitial : Q.initial ∉ Gamma.vertexSet Y) :
    IsFragmentOf Q.firstLink.path U := by
  exact hQ.isBracketAlternating.2 Q.firstLink Q.firstLink_mem_links
    (finite_firstLink_forward_of_bracketSafe hQ hinitial)

/-- Consequently the first link of an infinite bracket-safe trace is an
atomic fragment of the displayed forward family. -/
theorem infinite_firstLink_isFragmentOf
    {Q : InfiniteTrace Gamma.graph}
    (hQ : IsBracketSafe U Y (.infinite Q))
    (hinitial : Q.initial ∉ Gamma.vertexSet Y) :
    IsFragmentOf (Q.link 0).path U := by
  exact hQ.isBracketAlternating.2 (Q.link 0) Q.firstLink_mem_links
    (infinite_firstLink_forward_of_bracketSafe hQ hinitial)

/-- The exact endpoint obstruction: a one-link forward path which ends on
the reference warp cannot be safe relative to that reference warp.  Thus an
X-clean first hole fragment ending at a covered cut vertex is not by itself
a finite Claim-2 witness. -/
theorem not_isSafe_single_forward_of_exit_mem_reference
    (l : Link Gamma.graph) (hforward : l.direction = .forward)
    (hexit : l.exit ∈ Gamma.vertexSet Y) :
    ¬ IsSafe Y (.finite (.singleton l)) := by
  intro hsafe
  have hterminal : (AltPath.finite (FiniteTrace.singleton l)).terminal? =
      some l.exit := by simp
  have hlast : (AltPath.finite (FiniteTrace.singleton l)).lastDirection? =
      some .forward := by
    change some l.direction = some .forward
    rw [hforward]
  exact (hsafe.isAlternating.2.2.2 l.exit hterminal hlast) hexit

end LinkageBlueprint
end Blueprint
end Erdos599
