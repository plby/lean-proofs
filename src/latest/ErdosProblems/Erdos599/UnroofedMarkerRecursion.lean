/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerSuccessor

/-!
# The unroofed-marker ordinal construction

The new successor rule is run through the existing threadwise limit
operator. Its warp, growth and roof invariants are proved for every ordinal,
not supplied as a hypothetical ladder. Markers inserted at distinct stages
are distinct, and every scheduled vertex is roofed by that stage's successor.
The old Boolean slot is unused by this rule; marker absence is determined
afresh by actual roof exhaustion, never by a presumed terminal stage.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order
open KappaLadder

universe u

variable {V : Type u}

def step (G : DWeb V) (preferred : Ordinal.{u} → Option V)
    (o : Ordinal.{u}) (s : G.LadderAccumulationState) : G.LadderAccumulationState :=
  (successorFamily G (preferred o) s, true)

def state (G : DWeb V) (preferred : Ordinal.{u} → Option V)
    (o : Ordinal.{u}) : G.LadderAccumulationState :=
  G.ladderAccumulatedStateAux (step G preferred) o

def markerAt (G : DWeb V) (preferred : Ordinal.{u} → Option V)
    (o : Ordinal.{u}) : Option V :=
  selectMarker G (preferred o) (state G preferred o)

theorem state_succ (G : DWeb V) (preferred : Ordinal.{u} → Option V)
    (o : Ordinal.{u}) :
    state G preferred (o + 1) = step G preferred o (state G preferred o) := by
  simp only [state, DWeb.ladderAccumulatedStateAux,
    Ordinal.limitRecOn_add_one]

/-- All recursion invariants, with the local successor premises discharged. -/
theorem state_invariant (G : DWeb V) (preferred : Ordinal.{u} → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) (o : Ordinal.{u}) :
    CanonicalRecursionInvariant (G := G) (step G preferred) o := by
  apply recursionInvariant_all_of_step (step G preferred)
  · intro a s hwarp hself hsource
    exact successorFamily_isWarp G (preferred a) s hNoEnter hwarp hself hsource
  · intro a s
    exact successorFamily_grows G (preferred a) s
  · intro a s hwarp hself hsource
    exact successorFamily_roof_invariants G (preferred a) s
      hNoEnter hwarp hself hsource

theorem state_grows (G : DWeb V) (preferred : Ordinal.{u} → Option V)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Ordinal.{u}} (hab : a ≤ b) :
    G.LadderGrows (state G preferred a).1 (state G preferred b).1 := by
  rcases hab.lt_or_eq with hab | rfl
  · exact (state_invariant G preferred hNoEnter b).grows a hab
  · exact G.ladderGrows_refl _

theorem markerAt_not_mem_preMarkerRoof (G : DWeb V)
    (preferred : Ordinal.{u} → Option V) {a : Ordinal.{u}} {y : V}
    (hy : markerAt G preferred a = some y) :
    y ∉ G.roof (G.terminalFrontier (preMarker G (state G preferred a))) :=
  selectMarker_spec G (preferred a) (state G preferred a) hy

theorem markerAt_trivial_mem_successor (G : DWeb V)
    (preferred : Ordinal.{u} → Option V) {a : Ordinal.{u}} {y : V}
    (hy : markerAt G preferred a = some y) :
    G.trivialPath y ∈ (state G preferred (a + 1)).1 := by
  rw [state_succ]
  apply Or.inr
  simp only [markerFamily, show selectMarker G (preferred a)
    (state G preferred a) = some y from hy, Set.mem_singleton_iff]

theorem markerAt_essential_successor (G : DWeb V)
    (preferred : Ordinal.{u} → Option V) {a : Ordinal.{u}} {y : V}
    (hy : markerAt G preferred a = some y) :
    y ∈ G.essential (G.terminalFrontier (state G preferred (a + 1)).1) := by
  rw [state_succ]
  exact selectedMarker_essential G (preferred a) (state G preferred a) hy

/-- Every old marker is carried by each later warp. No finite termination
of the marker's component is asserted or needed. -/
theorem markerAt_mem_later_vertices (G : DWeb V)
    (preferred : Ordinal.{u} → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Ordinal.{u}} (hab : a < b) {y : V}
    (hy : markerAt G preferred a = some y) :
    y ∈ G.vertexSet (state G preferred b).1 := by
  have hsucc : a + 1 ≤ b := (Order.add_one_le_iff).mpr hab
  obtain ⟨p, hp, hprefix⟩ := state_grows G preferred hNoEnter hsucc
    (G.trivialPath y) (markerAt_trivial_mem_successor G preferred hy)
  exact ⟨p, hp, G.support_mono_of_extends hprefix (by simp)⟩

/-- Old markers are already roofed before every later marker is chosen. -/
theorem markerAt_mem_later_preMarkerRoof (G : DWeb V)
    (preferred : Ordinal.{u} → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Ordinal.{u}} (hab : a < b) {y : V}
    (hy : markerAt G preferred a = some y) :
    y ∈ G.roof (G.terminalFrontier (preMarker G (state G preferred b))) := by
  have hinv := state_invariant G preferred hNoEnter b
  apply G.roof_terminalFrontier_subset_canonicalArrow hNoEnter
    (state G preferred b) hinv.warp hinv.selfRoof hinv.sourceRoof
  exact hinv.selfRoof (markerAt_mem_later_vertices G preferred hNoEnter hab hy)

/-- In particular two different stages never insert the same marker. -/
theorem markerAt_stage_unique (G : DWeb V)
    (preferred : Ordinal.{u} → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a b : Ordinal.{u}} {y : V}
    (ha : markerAt G preferred a = some y)
    (hb : markerAt G preferred b = some y) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (markerAt_not_mem_preMarkerRoof G preferred hb
      (markerAt_mem_later_preMarkerRoof G preferred hNoEnter hab ha)).elim
  · exact hab
  · exact (markerAt_not_mem_preMarkerRoof G preferred ha
      (markerAt_mem_later_preMarkerRoof G preferred hNoEnter hba hb)).elim

/-- Scheduling a vertex guarantees its capture in the next roof: it is
either already roofed by the arrow or is precisely the selected marker. -/
theorem preferred_mem_successorRoof (G : DWeb V)
    (preferred : Ordinal.{u} → Option V) {a : Ordinal.{u}} {y : V}
    (hy : preferred a = some y) :
    y ∈ G.roof (G.terminalFrontier (state G preferred (a + 1)).1) := by
  classical
  by_cases hroof : y ∈ G.roof
      (G.terminalFrontier (preMarker G (state G preferred a)))
  · rw [state_succ]
    apply G.roof_mono ?_ hroof
    rintro z ⟨p, hp, hpz⟩
    exact ⟨p, Or.inl hp, hpz⟩
  · have hmarker : markerAt G preferred a = some y :=
      selectMarker_eq_preferred G (preferred a) (state G preferred a) hy hroof
    exact G.essential_subset_roof _ (markerAt_essential_successor G preferred hmarker)

#print axioms state_invariant
#print axioms markerAt_stage_unique
#print axioms preferred_mem_successorRoof

end Erdos599.DWeb.UnroofedMarker
