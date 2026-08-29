/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularContinuation
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# Splitting a singular row at a stop-over boundary

When a stop-over contains some current source vertices, endpoint purity does
not make the whole linkage terminal-clean: a nontrivial member may meet the
stop-over at both its initial and terminal vertices.  The members whose
initial vertices lie outside the stop-over do have the exact clean geometry
needed by the quotient continuation.  This file records that sound
restriction, without making any assertion about the complementary members.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularBoundarySplit

open SliceSpliceSource SingularContinuation

universe u

variable {V : Type u}

/-- The part of a source linkage which starts strictly outside its right
boundary. -/
def outsidePart (G : DWeb V) (W : Set G.DPath) (C : Set V) : Set G.DPath :=
  initialRestriction G W (G.source \ C)

@[simp] theorem mem_outsidePart {G : DWeb V} {W : Set G.DPath}
    {C : Set V} {p : G.DPath} :
    p ∈ outsidePart G W C ↔
      p ∈ W ∧ p.initial ∈ G.source \ C :=
  Iff.rfl

/-- Endpoint purity becomes terminal cleanliness after discarding the
members which start in the boundary. -/
theorem outsidePart_terminalClean
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W) :
    TerminalCleanAt G (outsidePart G W C) C := by
  intro p hp x hxp hxC
  obtain ⟨f, rfl, hends, _hsource⟩ := hW.endpointPure p hp.1
  have hxEnds : x ∈ ({f.start, f.finish} : Set V) := by
    rw [← hends]
    exact ⟨hxp, Or.inr hxC⟩
  have hxFinish : x = f.finish := by
    rcases Set.mem_insert_iff.1 hxEnds with hxStart | hxFinish
    · exfalso
      have hstartNotC :
          DirectedPath.Path.initial (Sum.inl f : G.DPath) ∉ C := hp.2.2
      change f.start ∉ C at hstartNotC
      exact hstartNotC (hxStart.symm ▸ hxC)
    · exact Set.mem_singleton_iff.1 hxFinish
  change some f.finish = some x
  exact congrArg some hxFinish.symm

/-- If the boundary separates the ambient source, every member starting
outside it lies wholly in its roof. -/
theorem outsidePart_vertexSet_subset_roof
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C) :
    G.vertexSet (outsidePart G W C) ⊆ G.roof C := by
  rintro x ⟨p, hp, hxp⟩
  apply G.pathSupportRoof p C
  · apply hsep
    exact hp.2.1
  · intro t ht
    exact hW.terminalFrontier_subset ⟨p, hp.1, ht⟩
  · intro y hy
    rw [outsidePart_terminalClean hW p hp y hy.1 hy.2]
    exact Set.mem_singleton y
  · exact hxp

/-- Restriction preserves the warp property. -/
theorem outsidePart_isWarp
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : G.IsWarp W) : G.IsWarp (outsidePart G W C) := by
  intro p hp q hq hpq
  exact hW hp.1 hq.1 hpq

/-- Restriction preserves finite character. -/
theorem outsidePart_finiteCharacter
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : G.HasFiniteCharacter W) :
    G.HasFiniteCharacter (outsidePart G W C) := by
  intro p hp
  exact hW hp.1

/-- Every old path belongs either to the clean outside part or starts in the
boundary.  The full-source hypothesis is used only to locate its initial
vertex in the ambient source. -/
theorem outsidePart_union_insidePart
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hW : G.initialSet W = G.source) :
    outsidePart G W C ∪ initialRestriction G W (G.source ∩ C) = W := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (fun _ h ↦ h.1) (fun _ h ↦ h.1)
  · intro p hp
    have hpSource : p.initial ∈ G.source := by
      rw [← hW]
      exact ⟨p, hp, rfl⟩
    by_cases hpC : p.initial ∈ C
    · exact Or.inr ⟨hp, hpSource, hpC⟩
    · exact Or.inl ⟨hp, hpSource, hpC⟩

/-! ## Terminal requests for the next quotient row -/

/-- The terminals of precisely those old components whose initial vertices
belong to the next designated source set. -/
def requestedFrontier (G : DWeb V) (W : Set G.DPath) (A : Set V) : Set V :=
  G.terminalFrontier (initialRestriction G W A)

/-- A chosen old component ending at one requested frontier vertex. -/
noncomputable def requestedPath
    (G : DWeb V) (W : Set G.DPath) (A : Set V)
    (x : requestedFrontier G W A) : G.DPath :=
  Classical.choose x.2

theorem requestedPath_spec
    (G : DWeb V) (W : Set G.DPath) (A : Set V)
    (x : requestedFrontier G W A) :
    requestedPath G W A x ∈ initialRestriction G W A ∧
      G.terminal? (requestedPath G W A x) = some x.1 :=
  Classical.choose_spec x.2

/-- Send a requested terminal back to the initial vertex of its unique old
component. -/
noncomputable def requestedInitial
    (G : DWeb V) (W : Set G.DPath) (A : Set V)
    (x : requestedFrontier G W A) : A :=
  ⟨(requestedPath G W A x).initial, (requestedPath_spec G W A x).1.2⟩

theorem requestedInitial_injective
    {G : DWeb V} {W : Set G.DPath} {A : Set V}
    (hW : G.IsWarp W) :
    Function.Injective (requestedInitial G W A) := by
  intro x y hxy
  have hinitial : (requestedPath G W A x).initial =
      (requestedPath G W A y).initial := congrArg Subtype.val hxy
  have hpath : requestedPath G W A x = requestedPath G W A y := by
    by_contra hne
    have hdis := hW
      (requestedPath_spec G W A x).1.1
      (requestedPath_spec G W A y).1.1 hne
    exact Set.disjoint_left.1 hdis
      (requestedPath G W A x).initial_mem_support
      (hinitial ▸ (requestedPath G W A y).initial_mem_support)
  apply Subtype.ext
  exact Option.some.inj <| calc
    some x.1 = G.terminal? (requestedPath G W A x) :=
      (requestedPath_spec G W A x).2.symm
    _ = G.terminal? (requestedPath G W A y) :=
      congrArg G.terminal? hpath
    _ = some y.1 := (requestedPath_spec G W A y).2

/-- The quotient request has cardinality no larger than the designated old
source set. -/
theorem mk_requestedFrontier_le
    {G : DWeb V} {W : Set G.DPath} {A : Set V}
    (hW : G.IsWarp W) :
    #(requestedFrontier G W A) ≤ #A :=
  Cardinal.mk_le_of_injective (requestedInitial_injective hW)

/-- Every designated old source has a finite old component and hence a
requested terminal.  This is the precise incidence relation used to pull
target links back from a quotient row. -/
theorem exists_path_to_requestedFrontier
    {G : DWeb V} {W : Set G.DPath} {D A : Set V}
    (hW : IsLinkageBetween G G.source D W)
    (hA : A ⊆ G.source) {a : V} (ha : a ∈ A) :
    ∃ p ∈ initialRestriction G W A,
      p.initial = a ∧
      ∃ t : requestedFrontier G W A, G.terminal? p = some t.1 := by
  have haInitial : a ∈ G.initialSet W := hW.initialSet_eq.symm ▸ hA ha
  obtain ⟨p, hpW, hpInitial⟩ := haInitial
  obtain ⟨f, rfl⟩ := hW.finiteCharacter hpW
  have hfA : DirectedPath.Path.initial (Sum.inl f : G.DPath) ∈ A :=
    hpInitial ▸ ha
  let t : requestedFrontier G W A :=
    ⟨f.finish, ⟨.inl f, ⟨hpW, hfA⟩, rfl⟩⟩
  exact ⟨.inl f, ⟨hpW, hfA⟩, hpInitial, t, rfl⟩

/-- Every designated old source is recovered from the requested terminal of
its unique old component. -/
theorem requestedInitial_surjective
    {G : DWeb V} {W : Set G.DPath} {D A : Set V}
    (hW : IsLinkageBetween G G.source D W)
    (hA : A ⊆ G.source) :
    Function.Surjective (requestedInitial G W A) := by
  rintro ⟨a, ha⟩
  obtain ⟨p, hp, hpInitial, t, hpTerminal⟩ :=
    exists_path_to_requestedFrontier hW hA ha
  have hpath : requestedPath G W A t = p := by
    by_contra hne
    have hdis := hW.isWarp
      (requestedPath_spec G W A t).1.1 hp.1 hne
    exact Set.disjoint_left.1 hdis
      (G.terminal_mem_support (requestedPath_spec G W A t).2)
      (G.terminal_mem_support hpTerminal)
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change (requestedPath G W A t).initial = a
  exact (congrArg (fun q : G.DPath ↦ q.initial) hpath).trans hpInitial

/-- A full linkage gives a bijective change of coordinates between a
designated source set and its old terminal frontier. -/
theorem mk_requestedFrontier_eq
    {G : DWeb V} {W : Set G.DPath} {D A : Set V}
    (hW : IsLinkageBetween G G.source D W)
    (hA : A ⊆ G.source) :
    #(requestedFrontier G W A) = #A := by
  apply le_antisymm
  · exact mk_requestedFrontier_le hW.isWarp
  · exact Cardinal.mk_le_of_surjective (requestedInitial_surjective hW hA)

end SingularBoundarySplit
end CardinalInduction
end Erdos599
