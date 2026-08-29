/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceResidualHallRoot
import Mathlib.Data.Fin.Rev

/-!
# Reversing finite-character families and coloured safe words

Directed duality transposes the graph as well as the chronological word.
The endpoint-prescribed consequence is intended for the finite Hall
exchange: it may change the source, but not the original forward family.
It does not by itself construct a simultaneous assignment.
-/

namespace Erdos599.Alternating.ColouredSafeFiniteDuality

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

def reverseWeb (Gamma : DWeb V) : DWeb V where
  graph := transpose Gamma.graph
  source := Gamma.target
  target := Gamma.source

def reverseFamily (W : Set Gamma.DPath) : Set (reverseWeb Gamma).DPath :=
  {q | ∃ p : FinitePath Gamma.graph, Sum.inl p ∈ W ∧ q = Sum.inl p.reverse}

theorem reverseFamily_isWarp {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) :
    (reverseWeb Gamma).IsWarp (reverseFamily W) := by
  rintro q ⟨p, hp, rfl⟩ r ⟨t, ht, rfl⟩ hne
  have hpt : (Sum.inl p : Gamma.DPath) ≠ Sum.inl t := by
    intro heq
    have hpt : p = t := Sum.inl.inj heq
    exact hne (hpt ▸ rfl)
  change Disjoint p.reverse.support t.reverse.support
  rw [DirectedPath.FinitePath.support_reverse, DirectedPath.FinitePath.support_reverse]
  exact hW hp ht hpt

theorem reverseFamily_finite (W : Set Gamma.DPath) :
    (reverseWeb Gamma).HasFiniteCharacter (reverseFamily W) := by
  rintro q ⟨p, hp, rfl⟩
  exact ⟨p.reverse, rfl⟩

theorem reverseFamily_vertexSet {W : Set Gamma.DPath}
    (hW : Gamma.HasFiniteCharacter W) :
    (reverseWeb Gamma).vertexSet (reverseFamily W) = Gamma.vertexSet W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, hx⟩
    change x ∈ p.reverse.support at hx
    rw [DirectedPath.FinitePath.support_reverse] at hx
    exact ⟨Sum.inl p, hp, hx⟩
  · rintro ⟨q, hq, hx⟩
    obtain ⟨p, rfl⟩ := hW hq
    refine ⟨Sum.inl p.reverse, ⟨p, hq, rfl⟩, ?_⟩
    change x ∈ p.reverse.support
    rw [DirectedPath.FinitePath.support_reverse]
    exact hx

theorem reverseFamily_initialSet (W : Set Gamma.DPath) :
    (reverseWeb Gamma).initialSet (reverseFamily W) = Gamma.terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨Sum.inl p, hp, congrArg some hx⟩
  · rintro ⟨q, hq, hx⟩
    cases q with
    | inl p => exact ⟨Sum.inl p.reverse, ⟨p, hq, rfl⟩, Option.some.inj hx⟩
    | inr r => cases hx

theorem reverseFamily_terminalFrontier {W : Set Gamma.DPath}
    (hW : Gamma.HasFiniteCharacter W) :
    (reverseWeb Gamma).terminalFrontier (reverseFamily W) = Gamma.initialSet W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨Sum.inl p, hp, Option.some.inj hx⟩
  · rintro ⟨q, hq, hx⟩
    obtain ⟨p, rfl⟩ := hW hq
    exact ⟨Sum.inl p.reverse, ⟨p, hq, rfl⟩, congrArg some hx⟩

theorem reverseFamily_edges {W : Set Gamma.DPath}
    (hW : Gamma.HasFiniteCharacter W) (x y : V) :
    (x, y) ∈ familyEdges (reverseFamily W) ↔ (y, x) ∈ familyEdges W := by
  constructor
  · intro he
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp he
    obtain ⟨⟨p, hp, rfl⟩, he⟩ := Set.mem_iUnion.mp hq
    exact Set.mem_iUnion.mpr ⟨Sum.inl p, Set.mem_iUnion.mpr
      ⟨hp, (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff p).mp he⟩⟩
  · intro he
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp he
    obtain ⟨hqW, he⟩ := Set.mem_iUnion.mp hq
    obtain ⟨p, rfl⟩ := hW hqW
    exact Set.mem_iUnion.mpr ⟨Sum.inl p.reverse, Set.mem_iUnion.mpr
      ⟨⟨p, hqW, rfl⟩, (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff p).mpr he⟩⟩

theorem finitePath_reverse_reverse {D : Digraph V} (p : FinitePath D) :
    p.reverse.reverse = p := by
  cases p
  simp [FinitePath.reverse]
  rfl

theorem reverseFamily_reverseFamily {W : Set Gamma.DPath}
    (hW : Gamma.HasFiniteCharacter W) : reverseFamily (reverseFamily W) = W := by
  ext q
  constructor
  · rintro ⟨p, ⟨r, hr, heq⟩, rfl⟩
    have hpr : p = r.reverse := Sum.inl.inj heq
    rw [hpr]
    exact (congrArg (fun t : FinitePath Gamma.graph ↦ (Sum.inl t : Gamma.DPath))
      (finitePath_reverse_reverse r)).symm ▸ hr
  · intro hq
    obtain ⟨p, rfl⟩ := hW hq
    exact ⟨p.reverse, ⟨p, hq, rfl⟩,
      congrArg Sum.inl (finitePath_reverse_reverse p).symm⟩

variable {W Y : Set Gamma.DPath}

/-- Reverse chronology and transpose the graph, keeping each edge colour.
This operation is only claimed for finite-character owners. -/
def reverseWord (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.HasFiniteCharacter W) (hY : Gamma.HasFiniteCharacter Y) :
    FiniteColouredOccurrenceWord (reverseFamily W) (reverseFamily Y) where
  length := Q.length
  vertex i := Q.vertex i.rev
  direction i := Q.direction i.rev
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i.rev with
    | forward =>
        simp only [Fin.rev_castSucc, Fin.rev_succ]
        apply (reverseFamily_edges hW _ _).mpr
        simpa only [hd] using Q.actualEdge_spec i.rev
    | backward =>
        simp only [Fin.rev_castSucc, Fin.rev_succ]
        apply (reverseFamily_edges hY _ _).mpr
        simpa only [hd] using Q.actualEdge_spec i.rev
  occurrence_injective := by
    intro i j heq
    have hd := congrArg Prod.fst heq
    change Q.direction i.rev = Q.direction j.rev at hd
    have he := congrArg (fun z : Direction × (V × V) ↦ z.2.swap) heq
    apply Fin.rev_injective
    apply Q.occurrence_injective
    apply Prod.ext hd
    cases hi : Q.direction i.rev <;> cases hj : Q.direction j.rev <;>
      simpa only [hi, hj, Fin.rev_castSucc, Fin.rev_succ, Prod.swap_prod_mk] using he

theorem reverseWord_first (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.HasFiniteCharacter W) (hY : Gamma.HasFiniteCharacter Y) :
    (reverseWord Q hW hY).vertex 0 = Q.vertex (Fin.last Q.length) := by
  exact congrArg Q.vertex (Fin.rev_zero Q.length)

theorem reverseWord_last (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.HasFiniteCharacter W) (hY : Gamma.HasFiniteCharacter Y) :
    (reverseWord Q hW hY).vertex (Fin.last Q.length) = Q.vertex 0 := by
  exact congrArg Q.vertex (Fin.rev_last Q.length)

theorem reverseWord_forwardEdges (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.HasFiniteCharacter W) (hY : Gamma.HasFiniteCharacter Y)
    (x y : V) : (x, y) ∈ (reverseWord Q hW hY).forwardEdges ↔
      (y, x) ∈ Q.forwardEdges := by
  constructor
  · rintro ⟨i, hi⟩
    have hd : Q.direction i.1.rev = .forward := i.2
    refine ⟨⟨i.1.rev, hd⟩, ?_⟩
    refine (Q.forwardEdge_eq ⟨i.1.rev, hd⟩).trans ?_
    have he := congrArg Prod.swap
      (((reverseWord Q hW hY).forwardEdge_eq i).symm.trans hi)
    change (Q.vertex i.1.castSucc.rev, Q.vertex i.1.succ.rev).swap = (y, x) at he
    simp only [Fin.rev_castSucc, Fin.rev_succ, Prod.swap_prod_mk] at he
    exact he
  · rintro ⟨i, hi⟩
    have hd : (reverseWord Q hW hY).direction i.1.rev = .forward := by
      simpa only [reverseWord, Fin.rev_rev] using i.2
    refine ⟨⟨i.1.rev, hd⟩, ?_⟩
    refine ((reverseWord Q hW hY).forwardEdge_eq ⟨i.1.rev, hd⟩).trans ?_
    change (Q.vertex i.1.rev.castSucc.rev, Q.vertex i.1.rev.succ.rev) = (x, y)
    have he := congrArg Prod.swap ((Q.forwardEdge_eq i).symm.trans hi)
    simpa only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev, Prod.swap_prod_mk] using he

theorem reverseWord_backwardEdges (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.HasFiniteCharacter W) (hY : Gamma.HasFiniteCharacter Y)
    (x y : V) : (x, y) ∈ (reverseWord Q hW hY).backwardEdges ↔
      (y, x) ∈ Q.backwardEdges := by
  constructor
  · rintro ⟨i, hi⟩
    have hd : Q.direction i.1.rev = .backward :=
      (reverseWord Q hW hY).backwardIndex_direction i
    refine ⟨⟨i.1.rev, by simp only [hd, ne_eq, reduceCtorEq, not_false_eq_true]⟩, ?_⟩
    refine (Q.backwardEdge_eq _).trans ?_
    have he := congrArg Prod.swap
      (((reverseWord Q hW hY).backwardEdge_eq i).symm.trans hi)
    change (Q.vertex i.1.succ.rev, Q.vertex i.1.castSucc.rev).swap = (y, x) at he
    simp only [Fin.rev_castSucc, Fin.rev_succ, Prod.swap_prod_mk] at he
    exact he
  · rintro ⟨i, hi⟩
    have hd : Q.direction i.1 = .backward := Q.backwardIndex_direction i
    have hd' : (reverseWord Q hW hY).direction i.1.rev ≠ .forward := by
      simpa only [reverseWord, Fin.rev_rev] using i.2
    refine ⟨⟨i.1.rev, hd'⟩, ?_⟩
    refine ((reverseWord Q hW hY).backwardEdge_eq ⟨i.1.rev, hd'⟩).trans ?_
    change (Q.vertex i.1.rev.succ.rev, Q.vertex i.1.rev.castSucc.rev) = (x, y)
    have he := congrArg Prod.swap ((Q.backwardEdge_eq i).symm.trans hi)
    simpa only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev, Prod.swap_prod_mk] using he

/-- The actual interval and contact-removal conditions survive reversal;
no arbitrary directed graph is identified with its transpose. -/
theorem reverseWord_isIntervalSafe
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.HasFiniteCharacter W) (hY : Gamma.HasFiniteCharacter Y) :
    (reverseWord Q hW hY).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b x hax hbx
    apply (reverseWord_backwardEdges Q hW hY _ _).mpr
    exact hQ.outgoing_removed ((reverseWord_forwardEdges Q hW hY _ _).mp hax)
      ((reverseFamily_edges hY _ _).mp hbx)
  · intro x a b hxa hxb
    apply (reverseWord_backwardEdges Q hW hY _ _).mpr
    exact hQ.incoming_removed ((reverseWord_forwardEdges Q hW hY _ _).mp hxa)
      ((reverseFamily_edges hY _ _).mp hxb)
  · rintro p ⟨r, hr, rfl⟩
    rcases hQ.intervals (Sum.inl r) hr with hempty | ⟨q, hqr, heq⟩
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨x, y⟩ ⟨hQe, hre⟩
      have hmem : (y, x) ∈ Q.backwardEdges ∩ r.edgeSet :=
        ⟨(reverseWord_backwardEdges Q hW hY _ _).mp hQe,
          (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff r).mp hre⟩
      exact Set.notMem_empty _ (hempty ▸ hmem)
    · obtain ⟨q, rfl⟩ := Path.finite_of_isSubpathOf_finite hqr
      right
      refine ⟨Sum.inl q.reverse, ?_, ?_⟩
      · constructor
        · change q.reverse.support ⊆ r.reverse.support
          rw [DirectedPath.FinitePath.support_reverse, DirectedPath.FinitePath.support_reverse]
          exact hqr.1
        · rintro ⟨x, y⟩ he
          apply (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff r).mpr
          exact hqr.2 ((SwitchingCore.FinitePath.mem_edgeSet_reverse_iff q).mp he)
      · ext ⟨x, y⟩
        change (x, y) ∈ (reverseWord Q hW hY).backwardEdges ∩ r.reverse.edgeSet ↔
          (x, y) ∈ q.reverse.edgeSet
        rw [Set.mem_inter_iff, reverseWord_backwardEdges,
          SwitchingCore.FinitePath.mem_edgeSet_reverse_iff,
          SwitchingCore.FinitePath.mem_edgeSet_reverse_iff]
        exact Set.ext_iff.mp heq (y, x)
  · intro x y hxy
    have h := hQ.endpoint_pure ((reverseWord_forwardEdges Q hW hY _ _).mp hxy)
    rw [reverseFamily_initialSet, reverseFamily_terminalFrontier hY]
    exact ⟨h.2, h.1⟩

/-- Finite carriers exclude every infinite coloured word, because
its literal colour--edge pairs are injective. -/
theorem not_infiniteWord_of_finite_carriers
    (hW : (Gamma.vertexSet W).Finite) (hY : (Gamma.vertexSet Y).Finite) :
    ¬Nonempty (InfiniteColouredOccurrenceWord W Y) := by
  rintro ⟨Q⟩
  have hWE : (familyEdges W).Finite :=
    (hW.prod hW).subset (familyEdges_subset_vertexSet_prod W)
  have hYE : (familyEdges Y).Finite :=
    (hY.prod hY).subset (familyEdges_subset_vertexSet_prod Y)
  let E : Set (Direction × (V × V)) :=
    ({.forward} ×ˢ familyEdges W) ∪ ({.backward} ×ˢ familyEdges Y)
  have hE : E.Finite :=
    ((Set.finite_singleton _).prod hWE).union ((Set.finite_singleton _).prod hYE)
  apply hE.not_infinite
  apply Set.infinite_of_injective_forall_mem Q.occurrence_injective
  intro n
  cases hd : Q.direction n with
  | forward =>
      exact Or.inl ⟨Set.mem_singleton _, by simpa only [hd] using Q.actualEdge_spec n⟩
  | backward =>
      exact Or.inr ⟨Set.mem_singleton _, by simpa only [hd] using Q.actualEdge_spec n⟩

/-- A prescribed exposed terminal in a finite region is reached safely
from some exposed original initial. The forward family never changes.
The two boundary hypotheses are exactly the dual single-source hypotheses. -/
theorem exists_safeWord_to_terminal
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hWV : (Gamma.vertexSet W).Finite) (hYV : (Gamma.vertexSet Y).Finite)
    (hterminals : Gamma.terminalFrontier Y ⊆ Gamma.terminalFrontier W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆ Gamma.initialSet Y)
    {t : V} (ht : t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y) :
    ∃ s ∈ Gamma.initialSet W \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
        Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t := by
  have hsource : (reverseWeb Gamma).initialSet (reverseFamily Y) ⊆
      (reverseWeb Gamma).initialSet (reverseFamily W) := by
    rw [reverseFamily_initialSet, reverseFamily_initialSet]
    exact hterminals
  have hpure : (reverseWeb Gamma).terminalFrontier (reverseFamily W) ∩
      (reverseWeb Gamma).vertexSet (reverseFamily Y) ⊆
        (reverseWeb Gamma).terminalFrontier (reverseFamily Y) := by
    rw [reverseFamily_terminalFrontier hWfin, reverseFamily_vertexSet hYfin,
      reverseFamily_terminalFrontier hYfin]
    exact hinitial
  have htI : t ∈ (reverseWeb Gamma).initialSet (reverseFamily W) := by
    rw [reverseFamily_initialSet]
    exact ht.1
  have htOff : t ∉ (reverseWeb Gamma).vertexSet (reverseFamily Y) := by
    rw [reverseFamily_vertexSet hYfin]
    exact ht.2
  have hno : ¬Nonempty (InfiniteColouredOccurrenceWord (reverseFamily W) (reverseFamily Y)) := by
    apply not_infiniteWord_of_finite_carriers
    · rw [reverseFamily_vertexSet hWfin]
      exact hWV
    · rw [reverseFamily_vertexSet hYfin]
      exact hYV
  obtain ⟨s, hs, _hroute⟩ :=
    ColouredSafeReverseReachability.exists_safeTerminal_residualPath_of_no_safeInfinite
      (reverseFamily_isWarp hW) (reverseFamily_isWarp hY)
      (reverseFamily_finite W) (reverseFamily_finite Y)
      hsource hpure htI htOff (fun ⟨Q, _, _⟩ ↦ hno ⟨Q⟩)
  obtain ⟨hsBoundary, Q, hQ, hfirst, hlast⟩ := hs
  have hsOriginal : s ∈ Gamma.initialSet W \ Gamma.vertexSet Y := by
    simpa only [reverseFamily_terminalFrontier hWfin,
      reverseFamily_vertexSet hYfin] using hsBoundary
  refine ⟨s, hsOriginal, ?_⟩
  have hresult : ∃ P : FiniteColouredOccurrenceWord
      (reverseFamily (reverseFamily W)) (reverseFamily (reverseFamily Y)),
      P.IsIntervalSafe ∧ P.vertex 0 = s ∧ P.vertex (Fin.last P.length) = t := by
    refine ⟨reverseWord Q (reverseFamily_finite W) (reverseFamily_finite Y),
      reverseWord_isIntervalSafe hQ (reverseFamily_finite W) (reverseFamily_finite Y),
      ?_, ?_⟩
    · exact (reverseWord_first Q _ _).trans hlast
    · exact (reverseWord_last Q _ _).trans hfirst
  change ∃ P : FiniteColouredOccurrenceWord (Gamma := Gamma)
      (reverseFamily (reverseFamily W)) (reverseFamily (reverseFamily Y)),
      P.IsIntervalSafe ∧ P.vertex 0 = s ∧ P.vertex (Fin.last P.length) = t at hresult
  rw [reverseFamily_reverseFamily hWfin, reverseFamily_reverseFamily hYfin] at hresult
  exact hresult

#print axioms reverseFamily_isWarp
#print axioms reverseFamily_edges
#print axioms reverseFamily_reverseFamily
#print axioms reverseWord_isIntervalSafe
#print axioms not_infiniteWord_of_finite_carriers
#print axioms exists_safeWord_to_terminal

end Erdos599.Alternating.ColouredSafeFiniteDuality
