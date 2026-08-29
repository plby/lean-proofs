/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderRoofRecursion

/-!
# The actual unroofed-marker successor rule

Unlike the historical candidate rule, this construction never inserts a
vertex already roofed by the pre-marker arrow. It uses the same concrete
maximal rung and arrow operation, and honours a preferred marker whenever
that vertex is unroofed. Absence of a marker means that the entire vertex
set is roofed, not merely that the preferred request was unavailable.

The successor is proved to be a self-roofing warp, to roof the original
sources, and to extend every old component. These are the local inputs to
the existing threadwise ordinal-limit construction. No linkability or
grounding theorem is a premise of the construction.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal

universe u

variable {V : Type u}

/-- The maximal-rung arrow before adjoining the optional marker. -/
def preMarker (G : DWeb V) (s : G.LadderAccumulationState) : Set G.DPath :=
  G.arrow s.1 (G.liftedLadderRungOfState s)

/-- Prefer the requested unroofed vertex; otherwise choose any unroofed
vertex, and return `none` exactly when no such vertex exists. -/
def selectMarker (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) : Option V := by
  classical
  exact if h : ∃ x, preferred = some x ∧
      x ∉ G.roof (G.terminalFrontier (preMarker G s)) then
    some (Classical.choose h)
  else if h : ∃ x, x ∉ G.roof (G.terminalFrontier (preMarker G s)) then
    some (Classical.choose h)
  else none

theorem selectMarker_spec (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) {y : V}
    (hy : selectMarker G preferred s = some y) :
    y ∉ G.roof (G.terminalFrontier (preMarker G s)) := by
  classical
  unfold selectMarker at hy
  split_ifs at hy with hpreferred hsome
  · exact (Option.some.inj hy) ▸ (Classical.choose_spec hpreferred).2
  · exact (Option.some.inj hy) ▸ Classical.choose_spec hsome

theorem selectMarker_eq_preferred (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) {y : V}
    (hpreferred : preferred = some y)
    (hy : y ∉ G.roof (G.terminalFrontier (preMarker G s))) :
    selectMarker G preferred s = some y := by
  classical
  have h : ∃ x, preferred = some x ∧
      x ∉ G.roof (G.terminalFrontier (preMarker G s)) :=
    ⟨y, hpreferred, hy⟩
  have hchoice : Classical.choose h = y :=
    Option.some.inj ((Classical.choose_spec h).1.symm.trans hpreferred)
  simp only [selectMarker, dif_pos h, hchoice]

theorem selectMarker_eq_none_iff (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) :
    selectMarker G preferred s = none ↔
      ∀ y, y ∈ G.roof (G.terminalFrontier (preMarker G s)) := by
  classical
  constructor
  · intro hnone y
    by_contra hy
    have hsome : ∃ x, x ∉ G.roof (G.terminalFrontier (preMarker G s)) := ⟨y, hy⟩
    unfold selectMarker at hnone
    split_ifs at hnone with hpreferred
  · intro hfull
    have hn : ¬ ∃ x, x ∉ G.roof (G.terminalFrontier (preMarker G s)) := by
      rintro ⟨x, hx⟩
      exact hx (hfull x)
    have hnp : ¬ ∃ x, preferred = some x ∧
        x ∉ G.roof (G.terminalFrontier (preMarker G s)) := by
      rintro ⟨x, _, hx⟩
      exact hx (hfull x)
    simp only [selectMarker, dif_neg hnp, dif_neg hn]

/-- The optional singleton family. Isolated markers are actual paths. -/
def markerFamily (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) : Set G.DPath :=
  match selectMarker G preferred s with
  | none => ∅
  | some y => {G.trivialPath y}

def successorFamily (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) : Set G.DPath :=
  preMarker G s ∪ markerFamily G preferred s

theorem markerFamily_isWarp (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) : G.IsWarp (markerFamily G preferred s) := by
  cases hm : selectMarker G preferred s with
  | none => simp [markerFamily, hm, DWeb.IsWarp]
  | some y =>
      rw [markerFamily, hm]
      exact Set.pairwiseDisjoint_singleton _ _

theorem markerFamily_selfRoofing (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) :
    G.vertexSet (markerFamily G preferred s) ⊆
      G.roof (G.terminalFrontier (markerFamily G preferred s)) := by
  rintro x ⟨p, hp, hxp⟩
  cases hm : selectMarker G preferred s with
  | none => simp [markerFamily, hm] at hp
  | some y =>
      have hpEq : p = G.trivialPath y := by simpa [markerFamily, hm] using hp
      subst p
      have hxy : x = y := by simpa using hxp
      subst x
      apply G.subset_roof
      exact ⟨G.trivialPath y, hp, G.terminal?_trivialPath y⟩

theorem successorFamily_grows (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) :
    G.LadderGrows s.1 (successorFamily G preferred s) := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ :=
    (G.forwardExtension_arrow s.1 (G.liftedLadderRungOfState s)).1 p hp
  exact ⟨q, Or.inl hq, hpq⟩

theorem successorFamily_isWarp (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.IsWarp (successorFamily G preferred s) := by
  have hpre : G.IsWarp (preMarker G s) :=
    G.isWarp_arrow hwarp (G.isWarp_liftedLadderRungOfState' s)
  have hpreRoof : G.vertexSet (preMarker G s) ⊆
      G.roof (G.terminalFrontier (preMarker G s)) :=
    G.canonicalArrow_self_roofing hNoEnter s hwarp hself hsource
  apply Set.PairwiseDisjoint.union hpre (markerFamily_isWarp G preferred s)
  intro p hp q hq _hpq
  cases hm : selectMarker G preferred s with
  | none => simp [markerFamily, hm] at hq
  | some y =>
      have hqEq : q = G.trivialPath y := by simpa [markerFamily, hm] using hq
      subst q
      rw [G.support_trivialPath]
      apply Set.disjoint_singleton_right.mpr
      intro hyp
      exact selectMarker_spec G preferred s hm (hpreRoof ⟨p, hp, hyp⟩)

theorem successorFamily_roof_invariants (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    (G.vertexSet (successorFamily G preferred s) ⊆
      G.roof (G.terminalFrontier (successorFamily G preferred s))) ∧
    (G.source ⊆ G.roof (G.terminalFrontier (successorFamily G preferred s))) := by
  have hpreRoof := G.canonicalArrow_self_roofing hNoEnter s hwarp hself hsource
  have holdRoof := G.roof_terminalFrontier_subset_canonicalArrow
    hNoEnter s hwarp hself hsource
  have hleft : G.terminalFrontier (preMarker G s) ⊆
      G.terminalFrontier (successorFamily G preferred s) := by
    rintro x ⟨p, hp, hpx⟩
    exact ⟨p, Or.inl hp, hpx⟩
  have hright : G.terminalFrontier (markerFamily G preferred s) ⊆
      G.terminalFrontier (successorFamily G preferred s) := by
    rintro x ⟨p, hp, hpx⟩
    exact ⟨p, Or.inr hp, hpx⟩
  constructor
  · rintro x ⟨p, hp, hxp⟩
    rcases hp with hp | hp
    · exact G.roof_mono hleft (hpreRoof ⟨p, hp, hxp⟩)
    · exact G.roof_mono hright (markerFamily_selfRoofing G preferred s ⟨p, hp, hxp⟩)
  · intro x hx
    exact G.roof_mono hleft (holdRoof (hsource hx))

/-- An inserted marker is immediately essential, even if it is isolated.
This rules out the same-stage singleton obstruction of the historical rule. -/
theorem selectedMarker_essential (G : DWeb V) (preferred : Option V)
    (s : G.LadderAccumulationState) {y : V}
    (hy : selectMarker G preferred s = some y) :
    y ∈ G.essential (G.terminalFrontier (successorFamily G preferred s)) := by
  have hyRoof := selectMarker_spec G preferred s hy
  have hyNot : y ∉ G.terminalFrontier (preMarker G s) :=
    fun h ↦ hyRoof (G.subset_roof _ h)
  have hfrontier : G.terminalFrontier (successorFamily G preferred s) =
      G.terminalFrontier (preMarker G s) ∪ {y} := by
    rw [successorFamily, G.terminalFrontier_union]
    congr 1
    ext z
    simp only [markerFamily, hy, DWeb.mem_terminalFrontier,
      Set.mem_singleton_iff, exists_eq_left, G.terminal?_trivialPath,
      Option.some.injEq, eq_comm]
  rw [hfrontier]
  refine ⟨Or.inr rfl, ?_⟩
  have hdiff : (G.terminalFrontier (preMarker G s) ∪ {y}) \ {y} =
      G.terminalFrontier (preMarker G s) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz | hz, hne⟩
      · exact hz
      · exact (hne hz).elim
    · intro hz
      exact ⟨Or.inl hz, fun heq ↦ hyNot (heq ▸ hz)⟩
  simpa only [hdiff] using hyRoof

#print axioms successorFamily_isWarp
#print axioms successorFamily_roof_invariants
#print axioms selectedMarker_essential

end Erdos599.DWeb.UnroofedMarker
