/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardFiniteClusterOccurrence
import ErdosProblems.Erdos599.AlternatingSourceAssertions

/-!
# Literal retained intervals inside one selected forward link

Two component-cluster entries on the same selected forward link can be
compared in the intrinsic order of that finite link.  The intervening
literal subpath is retained whenever its edge tails avoid the current
stopping frontier.  This is the local positive path datum used by the
finite-cluster compiler; no component-exchange conclusion is asserted here.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A finite subpath of a forward link is retained once its initial vertex
is reached and every edge tail of the subpath avoids the stopping frontier. -/
theorem finiteSubpath_edges_subset_retainedForwardAt
    (Q : AltPath Gamma.graph) (T : Set V) (l : Link Gamma.graph)
    (hl : l ∈ Q.links) (hldir : l.direction = .forward) (x : V)
    (hentry : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) l.path.start x)
    (q : FinitePath Gamma.graph) (hqStart : q.start = x)
    (hqEdges : q.edgeSet ⊆ l.path.edgeSet)
    (hnoTail : ∀ e ∈ q.edgeSet, e.1 ∉ T) :
    q.edgeSet ⊆ retainedForwardEdgesAt T Q := by
  intro e he
  have heTail : e.1 ∈ q.support :=
    (q.edgeSet_subset_support_prod he).1
  have hqReach : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ q.edgeSet) q.start e.1 :=
    GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      q (fun _ h ↦ h) heTail
  have hqStep : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) q.start e.1 := by
    apply Relation.ReflTransGen.mono
      (r := fun a b ↦ (a, b) ∈ q.edgeSet)
      (p := retainedForwardLinkStepAt T l)
    · intro a b hab
      exact ⟨hqEdges hab, hnoTail (a, b) hab⟩
    · exact hqReach
  refine ⟨l, hl, hldir, hqEdges he, hnoTail e he, ?_⟩
  have hqStep' : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) x e.1 := by
    simpa only [hqStart] using hqStep
  exact hentry.trans hqStep'

/-- Starting with one retained occurrence, a later head on the same link
determines a literal retained interval between the two heads. -/
theorem RetainedForwardOccurrence.exists_retainedHeadInterval
    {T : Set V} {Q : AltPath Gamma.graph} {e f : V × V}
    (O : RetainedForwardOccurrence T Q e)
    (_hf : f ∈ (O.trace.link O.linkIndex).path.edgeSet)
    (horder : FinitePath.OrderedOccurrence
      (O.trace.link O.linkIndex).path e.2 f.2)
    (hnoTail : ∀ g ∈
      ((O.trace.link O.linkIndex).path.between horder).edgeSet, g.1 ∉ T) :
    ∃ q : FinitePath Gamma.graph,
      q.start = e.2 ∧ q.finish = f.2 ∧
      q.IsSubpathOf (.inl (O.trace.link O.linkIndex).path : Gamma.DPath) ∧
      q.edgeSet ⊆ retainedForwardEdgesAt T Q := by
  let l := O.trace.link O.linkIndex
  let q := l.path.between horder
  have hl : l ∈ Q.links := by
    rw [O.path_eq]
    exact ⟨O.linkIndex, rfl⟩
  have hentryHead : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) l.path.start e.2 :=
    O.tail_reachable.tail ⟨O.edge_mem, O.tail_not_frontier⟩
  have hqRetained : q.edgeSet ⊆ retainedForwardEdgesAt T Q :=
    finiteSubpath_edges_subset_retainedForwardAt Q T l hl O.direction e.2
      hentryHead q (by simp [q, l])
      (l.path.between_edgeSet_subset horder) (by simpa [q] using hnoTail)
  exact ⟨q, by simp [q, l], by simp [q, l],
    l.path.between_isSubpathOf horder, hqRetained⟩

/-- If every edge tail between two distinct retained heads avoids `T`, one
of the two intrinsic link orders yields a literal retained head interval. -/
theorem exists_retainedHeadInterval_dichotomy
    {T : Set V} {Q : AltPath Gamma.graph} {e f : V × V}
    (Oe : RetainedForwardOccurrence T Q e)
    (Of : RetainedForwardOccurrence T Q f)
    (hlink : Of.trace.link Of.linkIndex = Oe.trace.link Oe.linkIndex)
    (hne : e.2 ≠ f.2)
    (hnoTail : ∀ g ∈ (Oe.trace.link Oe.linkIndex).path.edgeSet,
      g.1 ∉ T) :
    (∃ q : FinitePath Gamma.graph,
      q.start = e.2 ∧ q.finish = f.2 ∧
      q.edgeSet ⊆ retainedForwardEdgesAt T Q) ∨
    (∃ q : FinitePath Gamma.graph,
      q.start = f.2 ∧ q.finish = e.2 ∧
      q.edgeSet ⊆ retainedForwardEdgesAt T Q) := by
  have heHead : e.2 ∈ (Oe.trace.link Oe.linkIndex).path.support :=
    ((Oe.trace.link Oe.linkIndex).path.edgeSet_subset_support_prod Oe.edge_mem).2
  have hfMem : f ∈ (Oe.trace.link Oe.linkIndex).path.edgeSet := by
    rw [← hlink]
    exact Of.edge_mem
  have hfHead : f.2 ∈ (Oe.trace.link Oe.linkIndex).path.support :=
    ((Oe.trace.link Oe.linkIndex).path.edgeSet_subset_support_prod hfMem).2
  rcases (Oe.trace.link Oe.linkIndex).path.orderedOccurrence_or_reverse
      heHead hfHead hne with hef | hfe
  · left
    obtain ⟨hef⟩ := hef
    obtain ⟨q, hs, ht, _hsub, hret⟩ :=
      Oe.exists_retainedHeadInterval hfMem hef
        (fun g hg ↦ hnoTail g
          ((Oe.trace.link Oe.linkIndex).path.between_edgeSet_subset hef hg))
    exact ⟨q, hs, ht, hret⟩
  · right
    obtain ⟨hfe⟩ := hfe
    have hfe' : FinitePath.OrderedOccurrence
        (Of.trace.link Of.linkIndex).path f.2 e.2 := by
      rw [hlink]
      exact hfe
    have heMem' : e ∈ (Of.trace.link Of.linkIndex).path.edgeSet := by
      rw [hlink]
      exact Oe.edge_mem
    obtain ⟨q, hs, ht, _hsub, hret⟩ :=
      Of.exists_retainedHeadInterval heMem' hfe'
        (fun g hg ↦ hnoTail g (by
          rw [← hlink]
          exact (Of.trace.link Of.linkIndex).path.between_edgeSet_subset hfe' hg))
    exact ⟨q, hs, ht, hret⟩

#print axioms RetainedForwardOccurrence.exists_retainedHeadInterval
#print axioms exists_retainedHeadInterval_dichotomy

end GroundingErasedDecode
end Erdos599
