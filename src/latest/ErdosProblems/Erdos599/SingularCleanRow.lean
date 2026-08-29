/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension

/-!
# Terminal-clean singular rows

This file isolates the pruning operation needed before the quotient
continuation in the singular-cardinal construction.  A non-completed row
member whose initial vertex already belongs to the current stop-over is
replaced by the trivial path at that vertex.  Completed members are retained,
because in a normalized web they contain every witness used by
`LinksToTarget`.

There is one genuine side condition: retained completed members must already
be terminal-clean at the stop-over.  This does not follow from
`CertifiedTargetRowStage` alone (a completed path can start in the stop-over
and finish at a different target vertex).  The condition follows, for
example, when every source vertex in the stop-over is already a target.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExtension

universe u

variable {V : Type u}

/-- The old paths retained by terminal-clean pruning: all completed paths,
and the pending paths whose initial vertex is outside the stop-over. -/
def cleanRetainedPaths (G : DWeb V) (W : Set G.DPath) (C : Set V) :
    Set G.DPath :=
  completedPart G W ∪ {p | p ∈ pendingPart G W ∧ p.initial ∉ C}

/-- Initial vertices at which a pending path is replaced by a trivial path. -/
def cleanReplacementSources (G : DWeb V) (W : Set G.DPath) (C : Set V) :
    Set V :=
  G.initialSet (pendingPart G W) ∩ C

/-- Replace precisely the pending paths which start in the stop-over by
trivial paths, retaining all completed paths and all other pending paths. -/
def cleanRowPaths (G : DWeb V) (W : Set G.DPath) (C : Set V) :
    Set G.DPath :=
  cleanRetainedPaths G W C ∪
    G.trivialPath '' cleanReplacementSources G W C

theorem cleanRetainedPaths_subset (G : DWeb V) (W : Set G.DPath)
    (C : Set V) : cleanRetainedPaths G W C ⊆ W := by
  rintro p (hp | hp)
  · exact hp.1
  · exact hp.1.1

theorem completedPart_subset_cleanRowPaths (G : DWeb V)
    (W : Set G.DPath) (C : Set V) :
    completedPart G W ⊆ cleanRowPaths G W C := by
  intro p hp
  exact Or.inl (Or.inl hp)

theorem cleanRowPaths_isWarp
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : G.IsWarp W) :
  G.IsWarp (cleanRowPaths G W C) := by
  apply Set.PairwiseDisjoint.union
  · intro p hp q hq hpq
    exact hW (cleanRetainedPaths_subset G W C hp)
      (cleanRetainedPaths_subset G W C hq) hpq
  · exact G.isWarp_trivialPaths (cleanReplacementSources G W C)
  · intro p hp q hq hpq
    obtain ⟨a, haReplacement, rfl⟩ := hq
    obtain ⟨r, hrPending, hra⟩ := haReplacement.1
    have hrW : r ∈ W := hrPending.1
    have hpr : p ≠ r := by
      intro hEq
      subst r
      rcases hp with hpCompleted | hpOutside
      · exact hrPending.2 hpCompleted
      · exact hpOutside.2 (hra ▸ haReplacement.2)
    rw [G.support_trivialPath]
    apply Set.disjoint_singleton_right.2
    intro hap
    exact Set.disjoint_left.1
      (hW (cleanRetainedPaths_subset G W C hp) hrW hpr)
      hap (hra ▸ r.initial_mem_support)

theorem cleanRowPaths_finiteCharacter
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : G.HasFiniteCharacter W) :
    G.HasFiniteCharacter (cleanRowPaths G W C) := by
  intro p hp
  rcases hp with hpRetained | ⟨a, _ha, rfl⟩
  · exact hW (cleanRetainedPaths_subset G W C hpRetained)
  · exact ⟨DirectedPath.FinitePath.trivial G.graph a, rfl⟩

theorem cleanRowPaths_initialSet
    {G : DWeb V} {W : Set G.DPath} {C : Set V} :
    G.initialSet (cleanRowPaths G W C) = G.initialSet W := by
  apply Set.Subset.antisymm
  · rintro a ⟨p, hp, rfl⟩
    rcases hp with hpRetained | ⟨b, hbReplacement, rfl⟩
    · exact ⟨p, cleanRetainedPaths_subset G W C hpRetained, rfl⟩
    · obtain ⟨q, hqPending, hqb⟩ := hbReplacement.1
      exact ⟨q, hqPending.1, hqb.trans (G.initial_trivialPath b).symm⟩
  · rintro a ⟨p, hpW, hpa⟩
    by_cases hpCompleted : p ∈ completedPart G W
    · exact ⟨p, Or.inl (Or.inl hpCompleted), hpa⟩
    · have hpPending : p ∈ pendingPart G W := ⟨hpW, hpCompleted⟩
      by_cases hpC : p.initial ∈ C
      · refine ⟨G.trivialPath p.initial, Or.inr ?_, ?_⟩
        · exact ⟨p.initial, ⟨⟨p, hpPending, rfl⟩, hpC⟩, rfl⟩
        · exact (G.initial_trivialPath p.initial).trans hpa
      · exact ⟨p, Or.inl (Or.inr ⟨hpPending, hpC⟩), hpa⟩

theorem cleanRowPaths_terminalFrontier_subset
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : G.terminalFrontier W ⊆ C) :
    G.terminalFrontier (cleanRowPaths G W C) ⊆ C := by
  rintro x ⟨p, hp, hpx⟩
  rcases hp with hpRetained | ⟨a, haReplacement, rfl⟩
  · exact hW ⟨p, cleanRetainedPaths_subset G W C hpRetained, hpx⟩
  · have hax : a = x := by
      simpa only [G.terminal?_trivialPath, Option.some.injEq] using hpx
    exact hax ▸ haReplacement.2

/-- Cleaning preserves an exact stop-over frontier.  The only nontrivial
case is a pending member which starts in the stop-over.  Exactness makes
that start a terminal of some row member, and warp disjointness forces it
to be the terminal of the member being replaced; its trivial replacement
therefore has the same terminal. -/
theorem cleanRowPaths_terminalFrontier_eq
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : G.IsWarp W) (hfrontier : G.terminalFrontier W = C) :
    G.terminalFrontier (cleanRowPaths G W C) = C := by
  apply Set.Subset.antisymm
  · exact cleanRowPaths_terminalFrontier_subset hfrontier.le
  · intro x hxC
    have hxFrontier : x ∈ G.terminalFrontier W := hfrontier.symm ▸ hxC
    obtain ⟨p, hpW, hpx⟩ := hxFrontier
    by_cases hpCompleted : p ∈ completedPart G W
    · exact ⟨p, Or.inl (Or.inl hpCompleted), hpx⟩
    · have hpPending : p ∈ pendingPart G W := ⟨hpW, hpCompleted⟩
      by_cases hpC : p.initial ∈ C
      · have hpInitialFrontier : p.initial ∈ G.terminalFrontier W :=
          hfrontier.symm ▸ hpC
        have hpTerminalInitial : G.terminal? p = some p.initial :=
          terminalCleanAt_terminalFrontier_of_isWarp hW p hpW p.initial
            p.initial_mem_support hpInitialFrontier
        refine ⟨G.trivialPath p.initial, Or.inr ?_, ?_⟩
        · exact ⟨p.initial,
            ⟨⟨p, hpPending, rfl⟩, hpC⟩, rfl⟩
        · rw [G.terminal?_trivialPath]
          exact hpTerminalInitial.symm.trans hpx
      · exact ⟨p, Or.inl (Or.inr ⟨hpPending, hpC⟩), hpx⟩

theorem cleanRowPaths_endpointPure
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : ∀ p ∈ W, IsPathBetween G G.source C p) :
    ∀ p ∈ cleanRowPaths G W C, IsPathBetween G G.source C p := by
  intro p hp
  rcases hp with hpRetained | ⟨a, haReplacement, rfl⟩
  · exact hW p (cleanRetainedPaths_subset G W C hpRetained)
  · obtain ⟨q, hqPending, hqa⟩ := haReplacement.1
    have haSource : a ∈ G.source := by
      obtain ⟨f, rfl, _hends, _hsource⟩ := hW q hqPending.1
      rw [← hqa]
      have hstart : f.start ∈ f.support ∩ G.source := by
        rw [_hsource]
        exact Set.mem_singleton f.start
      exact hstart.2
    refine ⟨DirectedPath.FinitePath.trivial G.graph a, rfl, ?_, ?_⟩
    · rw [DirectedPath.FinitePath.support_trivial]
      simp [haSource, haReplacement.2]
    · rw [DirectedPath.FinitePath.support_trivial]
      simp [haSource]

theorem cleanRowPaths_isLinkageBetween
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W) :
    IsLinkageBetween G G.source C (cleanRowPaths G W C) := by
  refine ⟨cleanRowPaths_isWarp hW.isWarp,
    cleanRowPaths_finiteCharacter hW.finiteCharacter, ?_,
    cleanRowPaths_terminalFrontier_subset hW.terminalFrontier_subset,
    cleanRowPaths_endpointPure hW.endpointPure⟩
  rw [cleanRowPaths_initialSet, hW.initialSet_eq]

theorem cleanRowPaths_linksToTarget
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C A : Set V}
    (hlinks : LinksToTarget G W A) :
    LinksToTarget G (cleanRowPaths G W C) A := by
  intro a ha
  obtain ⟨p, hpCompleted, hpa⟩ :=
    linksToTarget_completedPart hNorm hlinks a ha
  exact ⟨p, completedPart_subset_cleanRowPaths G W C hpCompleted, hpa⟩

/-- Pending retained paths are terminal-clean: endpoint purity says that a
stop-over vertex on such a path is an endpoint, and the initial endpoint was
excluded by construction. -/
theorem terminalCleanAt_pendingOutside
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W) :
    SingularContinuation.TerminalCleanAt G
      {p | p ∈ pendingPart G W ∧ p.initial ∉ C} C := by
  intro p hp x hxp hxC
  obtain ⟨q, rfl, hends, _hsource⟩ := hW.endpointPure p hp.1.1
  have hxEnds : x ∈ ({q.start, q.finish} : Set V) := by
    rw [← hends]
    exact ⟨hxp, Or.inr hxC⟩
  rcases Set.mem_insert_iff.1 hxEnds with hxStart | hxFinish
  · exfalso
    apply hp.2
    change q.start ∈ C
    rw [← hxStart]
    exact hxC
  · have hxFinish' : x = q.finish := Set.mem_singleton_iff.1 hxFinish
    change some q.finish = some x
    exact congrArg some hxFinish'.symm

/-- The pruning is terminal-clean exactly up to the retained completed
members.  Their cleanliness is the sole additional premise. -/
theorem cleanRowPaths_terminalClean
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hCompleted : SingularContinuation.TerminalCleanAt G
      (completedPart G W) C) :
    SingularContinuation.TerminalCleanAt G (cleanRowPaths G W C) C := by
  intro p hp x hxp hxC
  rcases hp with (hpCompleted | hpPending) | ⟨a, _ha, rfl⟩
  · exact hCompleted p hpCompleted x hxp hxC
  · exact terminalCleanAt_pendingOutside hW p hpPending x hxp hxC
  · rw [G.support_trivialPath] at hxp
    have hxa : x = a := by simpa using hxp
    subst x
    exact G.terminal?_trivialPath a

/-- A useful sufficient condition for completed-path cleanliness.  If a
stop-over point on a completed path is its initial vertex, it is a source;
the overlap hypothesis makes it a target, and normalization forces it to be
the terminal. -/
theorem terminalCleanAt_completedPart_of_source_inter_stopover_subset_target
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hOverlap : G.source ∩ C ⊆ G.target) :
    SingularContinuation.TerminalCleanAt G (completedPart G W) C := by
  intro p hp x hxp hxC
  obtain ⟨q, rfl, hends, _hsource⟩ := hW.endpointPure p hp.1
  have hxEnds : x ∈ ({q.start, q.finish} : Set V) := by
    rw [← hends]
    exact ⟨hxp, Or.inr hxC⟩
  rcases Set.mem_insert_iff.1 hxEnds with hxStart | hxFinish
  · have hstartSource : q.start ∈ G.source := by
      rw [← hW.initialSet_eq]
      exact ⟨.inl q, hp.1, rfl⟩
    exact hNorm.terminal?_eq_of_mem_path (.inl q) hxp
      (hOverlap ⟨hxStart ▸ hstartSource, hxC⟩)
  · have hxFinish' : x = q.finish := Set.mem_singleton_iff.1 hxFinish
    change some q.finish = some x
    exact congrArg some hxFinish'.symm

/-- A certified row together with the terminal-clean invariant required by
the quotient continuation. -/
structure SingularCleanRow (G : DWeb V) (I : Type u)
    (rho : I → Cardinal.{u}) where
  certified : CertifiedTargetRowStage G I rho
  terminalClean : ∀ i, SingularContinuation.TerminalCleanAt G
    (certified.row.paths i) (certified.stopover i)

/-- Clean every column of a certified target row.  The stop-over,
separation certificate, height bound, source sets, and target links are
unchanged. -/
noncomputable def CertifiedTargetRowStage.toSingularCleanRow
    {G : DWeb V} (hNorm : G.IsNormalized)
    {I : Type u} {rho : I → Cardinal.{u}}
    (S : CertifiedTargetRowStage G I rho)
    (hCompleted : ∀ i, SingularContinuation.TerminalCleanAt G
      (completedPart G (S.row.paths i)) (S.stopover i)) :
    SingularCleanRow G I rho := by
  let T : TargetRowStage G I :=
    { sources := S.row.sources
      paths := fun i ↦ cleanRowPaths G (S.row.paths i) (S.stopover i)
      isWarp := fun i ↦ cleanRowPaths_isWarp (S.row.isWarp i)
      finiteCharacter := fun i ↦
        cleanRowPaths_finiteCharacter (S.row.finiteCharacter i)
      initialSet := fun i ↦ by
        rw [cleanRowPaths_initialSet, S.row.initialSet i]
      links := fun i ↦ cleanRowPaths_linksToTarget hNorm (S.row.links i) }
  let S' : CertifiedTargetRowStage G I rho :=
    { row := T
      stopover := S.stopover
      separating := fun i ↦
        { stopover :=
            { linkage := cleanRowPaths_isLinkageBetween
                (S.separating i).stopover.linkage
              minimal := (S.separating i).stopover.minimal
              quotient_unhindered :=
                (S.separating i).stopover.quotient_unhindered }
          separator := (S.separating i).separator }
      heightAtMost := S.heightAtMost
      frontier_eq := fun i ↦
        cleanRowPaths_terminalFrontier_eq (S.row.isWarp i)
          (S.frontier_eq i) }
  exact
    { certified := S'
      terminalClean := fun i ↦ cleanRowPaths_terminalClean
        (S.separating i).stopover.linkage (hCompleted i) }

/-- Columnwise source-overlap purity is enough to construct the clean row
without separately supplying completed-path cleanliness. -/
noncomputable def CertifiedTargetRowStage.toSingularCleanRow_of_overlap
    {G : DWeb V} (hNorm : G.IsNormalized)
    {I : Type u} {rho : I → Cardinal.{u}}
    (S : CertifiedTargetRowStage G I rho)
    (hOverlap : ∀ i, G.source ∩ S.stopover i ⊆ G.target) :
    SingularCleanRow G I rho :=
  S.toSingularCleanRow hNorm (fun i ↦
    terminalCleanAt_completedPart_of_source_inter_stopover_subset_target
      hNorm (S.separating i).stopover.linkage (hOverlap i))

@[simp] theorem toSingularCleanRow_sources
    {G : DWeb V} (hNorm : G.IsNormalized)
    {I : Type u} {rho : I → Cardinal.{u}}
    (S : CertifiedTargetRowStage G I rho)
    (hCompleted : ∀ i, SingularContinuation.TerminalCleanAt G
      (completedPart G (S.row.paths i)) (S.stopover i)) :
    (S.toSingularCleanRow hNorm hCompleted).certified.row.sources =
      S.row.sources := rfl

@[simp] theorem toSingularCleanRow_stopover
    {G : DWeb V} (hNorm : G.IsNormalized)
    {I : Type u} {rho : I → Cardinal.{u}}
    (S : CertifiedTargetRowStage G I rho)
    (hCompleted : ∀ i, SingularContinuation.TerminalCleanAt G
      (completedPart G (S.row.paths i)) (S.stopover i)) :
    (S.toSingularCleanRow hNorm hCompleted).certified.stopover =
      S.stopover := rfl

end SingularExtension
end CardinalInduction
end Erdos599
