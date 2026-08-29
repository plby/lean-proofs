/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardFiniteCluster

/-!
# Concrete occurrences for the finite forward component cluster

The finite component-cluster argument selects a literal retained forward
edge for every displaced component.  This file retains the missing ordered
route provenance: every such edge occurs on a named link of the finite
selected compression, at a named link index, and its tail is reached inside
that link before the stopping frontier.

This is deliberately only an occurrence bridge.  It makes no claim that a
single component exchange preserves the whole terminal frontier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace GroundingErasedDecode

/-- A retained forward edge together with its literal occurrence in the
finite selected compression.  The link index, the edge position inside the
link, and the prefix reachability before `T` are all retained. -/
structure RetainedForwardOccurrence (T : Set V)
    (Q : Alternating.AltPath Gamma.graph) (edge : V × V) where
  trace : Alternating.FiniteTrace Gamma.graph
  path_eq : Q = .finite trace
  linkIndex : Fin (trace.lastIndex + 1)
  direction : (trace.link linkIndex).direction = .forward
  edge_mem : edge ∈ (trace.link linkIndex).path.edgeSet
  edgeIndex : ℕ
  edgeIndex_bound :
    edgeIndex + 1 < (trace.link linkIndex).path.walk.support.length
  edge_eq : edge =
    ((trace.link linkIndex).path.walk.support[edgeIndex],
      (trace.link linkIndex).path.walk.support[edgeIndex + 1])
  tail_not_frontier : edge.1 ∉ T
  tail_reachable : Relation.ReflTransGen
    (retainedForwardLinkStepAt T (trace.link linkIndex))
    (trace.link linkIndex).path.start edge.1

/-- The alternating path of every erased compression is finite, because the
compression stores an actual terminal vertex. -/
theorem PopularAuxiliary.Input.ErasedSignedRoute.ErasedCompression.path_isFinite
    {x y : V} {raw : List (PopularAuxiliary.Input.SignedEdge V)}
    {E : PopularAuxiliary.Input.ErasedSignedRoute x y raw}
    (C : PopularAuxiliary.Input.ErasedSignedRoute.ErasedCompression
      (Gamma := Gamma) E) : C.path.IsFinite := by
  rw [Alternating.AltPath.isFinite_iff_exists_terminal]
  exact ⟨y, C.terminal_eq⟩

/-- Membership in the retained relation of a finite alternating path has a
literal finite-trace occurrence. -/
theorem exists_retainedForwardOccurrence
    {T : Set V} {Q : Alternating.AltPath Gamma.graph}
    (hfinite : Q.IsFinite) {e : V × V}
    (he : e ∈ retainedForwardEdgesAt T Q) :
    Nonempty (RetainedForwardOccurrence T Q e) := by
  rcases he with ⟨l, hl, hdir, hedge, htail, hreach⟩
  cases hQ : Q with
  | trivial v =>
      simp only [hQ, Alternating.AltPath.links_trivial] at hl
      simp at hl
  | finite trace =>
      simp only [hQ, Alternating.AltPath.links,
        Alternating.FiniteTrace.links, Set.mem_range] at hl
      obtain ⟨i, rfl⟩ := hl
      have hedge' : e ∈ (trace.link i).path.walk.edgeSet := hedge
      rw [Alternating.Walk.mem_edgeSet_iff_exists_getVert] at hedge'
      obtain ⟨n, hn, hnSupport, hedgeEq⟩ := hedge'
      exact ⟨{
        trace := trace
        path_eq := rfl
        linkIndex := i
        direction := hdir
        edge_mem := hedge
        edgeIndex := n
        edgeIndex_bound := hnSupport
        edge_eq := hedgeEq
        tail_not_frontier := htail
        tail_reachable := hreach }⟩
  | infinite trace =>
      simp only [hQ, Alternating.AltPath.IsFinite] at hfinite

/-- The chronological position of a retained occurrence in its finite
selected compression: first the link index, then the directed edge index
inside that link. -/
def RetainedForwardOccurrence.routePosition
    {T : Set V} {Q : Alternating.AltPath Gamma.graph} {e : V × V}
    (X : RetainedForwardOccurrence T Q e) : ℕ × ℕ :=
  (X.linkIndex.1, X.edgeIndex)

/-- A route position determines the literal ambient edge.  This is the
strict progress fact needed to order the injected component cluster. -/
theorem RetainedForwardOccurrence.edge_eq_of_routePosition_eq
    {T : Set V} {Q : Alternating.AltPath Gamma.graph} {e f : V × V}
    (X : RetainedForwardOccurrence T Q e)
    (Y : RetainedForwardOccurrence T Q f)
    (hpos : X.routePosition = Y.routePosition) : e = f := by
  rcases X with ⟨traceX, hQX, iX, hdirX, hmemX, nX, hnX,
    hedgeX, htailX, hreachX⟩
  rcases Y with ⟨traceY, hQY, iY, hdirY, hmemY, nY, hnY,
    hedgeY, htailY, hreachY⟩
  have htrace : traceX = traceY :=
    Alternating.AltPath.finite.inj (hQX.symm.trans hQY)
  subst traceY
  have hlinkVal : iX.1 = iY.1 := congrArg Prod.fst hpos
  have hlink : iX = iY := Fin.ext hlinkVal
  subst iY
  have hedgeIndex : nX = nY := congrArg Prod.snd hpos
  subst nY
  exact hedgeX.trans hedgeY.symm

/-- An injective selection of retained edges upgrades to an injective
selection of concrete finite-trace occurrences.  Edge membership in the
assigned displaced component is preserved exactly. -/
theorem exists_injective_retainedForwardOccurrences
    {T : Set V} {Q : Alternating.AltPath Gamma.graph}
    (hfinite : Q.IsFinite)
    {C : Type*} (componentEdges : C → Set (V × V))
    (hentry : ∃ entry : C → {e // e ∈ retainedForwardEdgesAt T Q},
      Function.Injective entry ∧
        ∀ c, (entry c).1 ∈ componentEdges c) :
    ∃ occurrence : C → Σ e, RetainedForwardOccurrence T Q e,
      Function.Injective (fun c ↦ (occurrence c).1) ∧
        ∀ c, (occurrence c).1 ∈ componentEdges c := by
  obtain ⟨entry, hentryInjective, hentryMem⟩ := hentry
  have hexists : ∀ c, Nonempty (RetainedForwardOccurrence T Q (entry c).1) := by
    intro c
    exact exists_retainedForwardOccurrence hfinite (entry c).2
  let occurrence : C → Σ e, RetainedForwardOccurrence T Q e := fun c ↦
    ⟨(entry c).1, Classical.choice (hexists c)⟩
  refine ⟨occurrence, ?_, ?_⟩
  · intro c d hcd
    apply hentryInjective
    exact Subtype.ext hcd
  · intro c
    exact hentryMem c

/-- The same selection is injective already at the concrete chronological
route position `(link index, edge index)`.  Thus displaced components can be
processed in the literal order of the one finite selected compression. -/
theorem exists_injective_retainedForwardRoutePositions
    {T : Set V} {Q : Alternating.AltPath Gamma.graph}
    (hfinite : Q.IsFinite)
    {C : Type*} (componentEdges : C → Set (V × V))
    (hentry : ∃ entry : C → {e // e ∈ retainedForwardEdgesAt T Q},
      Function.Injective entry ∧
        ∀ c, (entry c).1 ∈ componentEdges c) :
    ∃ occurrence : C → Σ e, RetainedForwardOccurrence T Q e,
      Function.Injective (fun c ↦ (occurrence c).2.routePosition) ∧
        ∀ c, (occurrence c).1 ∈ componentEdges c := by
  obtain ⟨occurrence, hedgeInjective, hmem⟩ :=
    exists_injective_retainedForwardOccurrences hfinite componentEdges hentry
  refine ⟨occurrence, ?_, hmem⟩
  intro c d hposition
  apply hedgeInjective
  exact (occurrence c).2.edge_eq_of_routePosition_eq
    (occurrence d).2 hposition

end GroundingErasedDecode
end Erdos599

#print axioms
  Erdos599.GroundingErasedDecode.exists_retainedForwardOccurrence
#print axioms
  Erdos599.GroundingErasedDecode.exists_injective_retainedForwardOccurrences
#print axioms
  Erdos599.GroundingErasedDecode.exists_injective_retainedForwardRoutePositions
