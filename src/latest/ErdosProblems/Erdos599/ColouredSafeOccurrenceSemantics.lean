/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeCountableAssignment
import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch
import ErdosProblems.Erdos599.InfiniteColouredOccurrenceEndpointBalance
import ErdosProblems.Erdos599.InfiniteColouredOccurrenceSwitch

/-!
# Relational semantics of a current safe occurrence

`CurrentSafeOccurrence` deliberately stores a coloured occurrence word rather
than coercing it to the more restrictive `AltPath` type.  This file exposes
the semantics which is common to its finite and infinite branches: literal
carrier and colour relations, the switched edge relation, and the exact
finite-character warp realized by that relation.

The finite degeneracy theorem is the relational form of the source's
common-forward-owner observation.  No alternating-path compiler, Hall
selection, or fixed-original-forward assertion is made here.
-/

noncomputable section

open Set

namespace Erdos599

namespace Alternating.InfiniteColouredOccurrenceWord.IsIntervalSafe

open DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- An arbitrary infinite interval-safe occurrence realizes a finite-character
warp with one new initial and no new terminal.  The pointwise balance used
here is the general occurrence-word theorem, not a prefix-chain hypothesis. -/
theorem exists_oneInitial_warp
    {Q : InfiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hstart : Q.vertex 0 ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {Q.vertex 0} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y := by
  let E := (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) :=
    biUnique_of_incident_reference_edges_removed hW hY
      Q.forwardEdges_subset_familyEdges
      hQ.incoming_removed hQ.outgoing_removed
  have hiso : ∀ x ∈ isolatedVertices Y, ∀ y,
      (x, y) ∉ E ∧ (y, x) ∉ E := by
    intro x hx y
    have hxInitial : x ∈ Gamma.initialSet Y :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    have hxTerminal : x ∈ Gamma.terminalFrontier Y :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    constructor
    · rintro (he | he)
      · exact not_isolated_of_hasOutgoing hY ⟨y, he.1⟩ hx
      · exact (hQ.endpoint_pure he).2 hxTerminal
    · rintro (he | he)
      · exact not_isolated_of_hasIncoming hY ⟨y, he.1⟩ hx
      · exact (hQ.endpoint_pure he).1 hxInitial
  obtain ⟨U, hU, hUE, hUI, hUfin⟩ :=
    exists_finiteWarp_realizing_incidence_intervalSwitch hW hY hWfin hYfin
      Q.forwardEdges_subset_familyEdges
      hQ.incoming_removed hQ.outgoing_removed rfl hbi
      hQ.intervals hQ.endpoint_pure (isolatedVertices Y) hiso
  have hbalance : ∀ x, edgeBalance (familyEdges U) x =
      edgeBalance (familyEdges Y) x + propInt (x = Q.vertex 0) := by
    intro x
    rw [hUE, edgeBalance_eq_of_incidence hW hY
      Q.backwardEdges_subset_familyEdges Q.forwardEdges_subset_familyEdges
      hQ.incoming_removed hQ.outgoing_removed]
    have hd := Q.edgeBalance_forward_sub_backward hW hY x
    omega
  have hboundary := boundary_eq_of_one_initial_balance hY hU hYfin hUfin
    hUI hstart hbalance
  exact ⟨U, hU, hUfin, hUE, hUI, hboundary⟩

end Alternating.InfiniteColouredOccurrenceWord.IsIntervalSafe

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {current Y : Set Gamma.DPath} {s t : V}

/-- The removed reference edges of either kind of occurrence. -/
def backwardEdges (A : CurrentSafeOccurrence current Y s) : Set (V × V) :=
  match A with
  | .infinite Q .. => Q.backwardEdges
  | .finite _ Q .. => Q.backwardEdges

/-- All ambient vertices appearing chronologically in the occurrence. -/
def vertexSet (A : CurrentSafeOccurrence current Y s) : Set V :=
  match A with
  | .infinite Q .. => Q.vertexSet
  | .finite _ Q .. => Q.vertexSet

/-- The exact relation obtained by retaining the unused reference edges and
inserting the forward-colour edges. -/
def switchedEdges (A : CurrentSafeOccurrence current Y s) : Set (V × V) :=
  (familyEdges Y \ A.backwardEdges) ∪ A.forwardEdges

theorem vertexSet_countable (A : CurrentSafeOccurrence current Y s) :
    A.vertexSet.Countable := by
  cases A with
  | infinite Q => exact Q.vertexSet_countable
  | finite t Q => exact Q.vertexSet_countable

theorem backwardEdges_countable (A : CurrentSafeOccurrence current Y s) :
    A.backwardEdges.Countable := by
  cases A with
  | infinite Q => exact Q.backwardEdges_countable
  | finite t Q => exact Q.backwardEdges_countable

theorem source_mem_vertexSet (A : CurrentSafeOccurrence current Y s) :
    s ∈ A.vertexSet := by
  cases A with
  | infinite Q hsafe hfirst =>
      exact ⟨0, hfirst⟩
  | finite t Q hsafe hfirst hlast =>
      exact ⟨0, hfirst⟩

/-- Relational finite degeneracy at `t`: the switched relation contains an
actual directed path from the indexed occurrence source to `t`. -/
def HasFiniteSwitchedPathTo
    (A : CurrentSafeOccurrence current Y s) (t : V) : Prop :=
  ∃ p : FinitePath Gamma.graph,
    p.start = s ∧ p.finish = t ∧ p.edgeSet ⊆ A.switchedEdges

/-- Exact common-forward-owner consequence of finite occurrence degeneracy. -/
theorem finiteDegenerate_endpoints_same_forward_owner
    (A : CurrentSafeOccurrence current Y s)
    (hcurrent : Gamma.IsWarp current) (hY : Gamma.IsWarp Y)
    (hterminal : A.terminal? = some t) (hne : s ≠ t)
    (hstart : s ∉ Gamma.vertexSet Y) (hfinish : t ∉ Gamma.vertexSet Y)
    (hdeg : A.HasFiniteSwitchedPathTo t) :
    ∃ q ∈ current, s ∈ q.support ∧ t ∈ q.support := by
  cases A with
  | infinite Q hsafe hfirst =>
      simp [terminal?] at hterminal
  | finite u Q hsafe hfirst hlast =>
      have hut : u = t := Option.some.inj hterminal
      obtain ⟨p, hpstart, hpfinish, hp⟩ := hdeg
      have hpstartQ : p.start = Q.vertex 0 := hpstart.trans hfirst.symm
      have hpfinishQ : p.finish = Q.vertex (Fin.last Q.length) :=
        (hpfinish.trans hut.symm).trans hlast.symm
      have hneQ : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length) := by
        intro h
        apply hne
        exact hfirst.symm.trans (h.trans (hlast.trans hut))
      have hstartQ : Q.vertex 0 ∉ Gamma.vertexSet Y := by
        simpa only [hfirst] using hstart
      have hfinishQ : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y := by
        simpa only [hlast, hut] using hfinish
      obtain ⟨q, hq, hqs, hqt⟩ :=
        hsafe.degenerate_endpoints_same_forward_owner hcurrent hY p
          hpstartQ hpfinishQ hneQ hstartQ hfinishQ hp
      exact ⟨q, hq, by simpa only [hfirst] using hqs,
        by simpa only [hlast, hut] using hqt⟩

/-- Exact finite-branch switch semantics, stated on the sum type consumed by
the successive assignment. -/
theorem exists_finiteWarp_of_terminal
    (A : CurrentSafeOccurrence current Y s)
    (hcurrent : Gamma.IsWarp current)
    (hcurrentFinite : Gamma.HasFiniteCharacter current)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hterminal : A.terminal? = some t) (hne : s ≠ t)
    (hstart : s ∉ Gamma.vertexSet Y) (hfinish : t ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = A.switchedEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y ∪ {t} := by
  cases A with
  | infinite Q hsafe hfirst =>
      simp [terminal?] at hterminal
  | finite u Q hsafe hfirst hlast =>
      have hut : u = t := Option.some.inj hterminal
      obtain ⟨U, hU, hUfin, hUE, hUI, hUinitial, hUterminal⟩ :=
        hsafe.exists_augmenting_warp hcurrent hY hcurrentFinite hYfinite
          (by
            intro h
            apply hne
            exact hfirst.symm.trans (h.trans (hlast.trans hut)))
          (by simpa only [hfirst] using hstart)
          (by simpa only [hlast, hut] using hfinish)
      exact ⟨U, hU, hUfin, hUE, hUI,
        by simpa only [hfirst] using hUinitial,
        by simpa only [hlast, hut] using hUterminal⟩

/-- Exact infinite-branch switch semantics.  No finite-prefix-chain field is
needed: general infinite occurrence balance supplies the one source defect. -/
theorem exists_finiteWarp_of_infinite
    (A : CurrentSafeOccurrence current Y s)
    (hcurrent : Gamma.IsWarp current)
    (hcurrentFinite : Gamma.HasFiniteCharacter current)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinfinite : A.terminal? = none) (hstart : s ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = A.switchedEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y := by
  cases A with
  | infinite Q hsafe hfirst =>
      obtain ⟨U, hU, hUfin, hUE, hUI, hUinitial, hUterminal⟩ :=
        hsafe.exists_oneInitial_warp hcurrent hY hcurrentFinite hYfinite
          (by simpa only [hfirst] using hstart)
      exact ⟨U, hU, hUfin, hUE, hUI,
        by simpa only [hfirst] using hUinitial, hUterminal⟩
  | finite t Q hsafe hfirst hlast =>
      simp [terminal?] at hinfinite

#print axioms Alternating.InfiniteColouredOccurrenceWord.IsIntervalSafe.exists_oneInitial_warp
#print axioms vertexSet_countable
#print axioms finiteDegenerate_endpoints_same_forward_owner
#print axioms exists_finiteWarp_of_terminal
#print axioms exists_finiteWarp_of_infinite

end ColouredSafeReverseReachability.CurrentSafeOccurrence

end Erdos599
