/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRelaxedCorridor
import ErdosProblems.Erdos599.GroundingPointwiseSwitch
import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport

/-!
# The last ladder contact on a finite ambient path

Assertion 8.18 repeatedly chooses the last earlier point of the finite
source--frontier path which lies on the limiting ladder.  This file isolates
that finite maximum, including the open-interval exclusion used by the
forward-corridor compiler.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingLastContact

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

/-- Before every positive position, if position zero lies on the ladder,
there is a last ladder position.  No position strictly between it and the
given bound lies on the ladder. -/
theorem exists_last_ladder_position_before
    (L : Input Gamma I) (R : FinitePath Gamma.graph)
    (i : Fin R.walk.support.length) (hi : 0 < i.1)
    (hzero : R.start ∈ Gamma.vertexSet L.ladder.paths) :
    ∃ j : Fin R.walk.support.length,
      j.1 < i.1 ∧
        R.walk.support[j] ∈ Gamma.vertexSet L.ladder.paths ∧
        ∀ k : Fin R.walk.support.length,
          j.1 < k.1 → k.1 < i.1 →
            R.walk.support[k] ∉ Gamma.vertexSet L.ladder.paths := by
  classical
  let contacts : Finset (Fin R.walk.support.length) :=
    Finset.univ.filter fun j ↦
      j.1 < i.1 ∧ R.walk.support[j] ∈ Gamma.vertexSet L.ladder.paths
  let z : Fin R.walk.support.length :=
    ⟨0, R.support_length_pos⟩
  have hzeroElem : z ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hi
    · have hhead : R.walk.support[z] =
          R.start := by
          calc
            R.walk.support[z] =
                R.walk.support.head R.walk.support_ne_nil := by
              exact List.getElem_zero R.support_length_pos
            _ = R.start := R.walk.head_support
      simpa only [hhead] using hzero
  let j : Fin R.walk.support.length :=
    contacts.max' ⟨z, hzeroElem⟩
  have hjContact : j ∈ contacts :=
    Finset.max'_mem contacts ⟨z, hzeroElem⟩
  have hjSpec : j.1 < i.1 ∧
      R.walk.support[j] ∈ Gamma.vertexSet L.ladder.paths := by
    simpa only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
      using hjContact
  refine ⟨j, hjSpec.1, hjSpec.2, ?_⟩
  intro k hjk hki hkLadder
  have hkContact : k ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hki, hkLadder⟩
  have hle : k ≤ j :=
    Finset.le_max' contacts k hkContact
  exact (not_le_of_gt hjk) hle

/-- A source--frontier path whose terminal is its first frontier point lies
in the roof used to define `offLadder`. -/
theorem support_subset_roofRegion_of_no_terminal_before
    (L : Input Gamma I) (R : FinitePath Gamma.graph)
    (hterminalSeparator : Popular.IsSeparator Gamma L.terminalCut)
    (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∈ L.terminalCut)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ L.terminalCut) :
    R.support ⊆ L.roofRegion := by
  have hstartRoof : R.start ∈ Gamma.roof L.terminalCut := by
    intro p hp
    exact hterminalSeparator p (hp.1 ▸ hsource) hp.2
  have hterminal : ∀ t,
      Gamma.terminal? (.inl R : Gamma.DPath) = some t →
        t ∈ L.terminalCut := by
    intro t ht
    have hrt : R.finish = t := by
      exact Option.some.inj ht
    simpa only [hrt] using hfinish
  have hinter :
      (DirectedPath.Path.support (.inl R : Gamma.DPath) ∩
          L.terminalCut) ⊆ ({R.finish} : Set V) := by
    intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxf
    have hxlast : x ≠
        R.walk.support.getLast R.walk.support_ne_nil := by
      simpa only [R.walk.getLast_support] using hxf
    have hxdrop : x ∈ R.walk.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast
    exact hfirst hxdrop hx.2
  have hroof := Gamma.pathSupportRoof
    (.inl R : Gamma.DPath) L.terminalCut hstartRoof hterminal hinter
  exact hroof

/-- A surviving fragment which contains the initial vertex of its parent
also starts there.  Otherwise the fragment would contain an edge entering
the parent initial vertex, impossible on a directed simple path or ray. -/
theorem fragment_initial_eq_parent_initial
    (L : Input Gamma I) (P : L.Fragment)
    (hmem : P.parent.initial ∈ P.path.support) :
    P.path.initial = P.parent.initial := by
  by_contra hne
  have hreverse : P.parent.initial ≠ P.path.initial :=
    fun h ↦ hne h.symm
  obtain ⟨y, hy⟩ : ∃ y, (y, P.parent.initial) ∈ P.path.edgeSet := by
    cases hpath : P.path with
    | inl p =>
        have hmem' : P.parent.initial ∈ p.support := by
          simpa only [hpath, DirectedPath.Path.support] using hmem
        have hne' : P.parent.initial ≠ p.start := by
          simpa only [hpath, DirectedPath.Path.initial] using hreverse
        obtain ⟨y, hy⟩ :=
          Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            p hmem' hne'
        exact ⟨y, by simpa only [hpath, DirectedPath.Path.edgeSet] using hy⟩
    | inr r =>
        have hmem' : P.parent.initial ∈ r.support := by
          simpa only [hpath, DirectedPath.Path.support] using hmem
        have hne' : P.parent.initial ≠ r.initial := by
          simpa only [hpath, DirectedPath.Path.initial] using hreverse
        obtain ⟨y, hy⟩ :=
          _root_.Erdos599.Alternating.Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial
            r hmem' hne'
        exact ⟨y, by simpa only [hpath, DirectedPath.Path.edgeSet] using hy⟩
  have hyParent : (y, P.parent.initial) ∈ P.parent.edgeSet :=
    P.edges_subset hy
  exact DWeb.KappaLadder.path_edge_head_ne_initial hyParent rfl

end GroundingLastContact
end Erdos599
