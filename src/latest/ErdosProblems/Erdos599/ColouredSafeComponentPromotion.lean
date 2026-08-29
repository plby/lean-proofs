/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeCountableAssignment
import ErdosProblems.Erdos599.SimultaneousAssignment

/-!
# Promoting coloured-safe words from one alternating component

Restriction to a component changes the reference-warp parameter of an
occurrence word.  This file proves the honest promotion back to the full
reference warp.  The proof uses component closure at every new reference
incidence; it does not identify the restricted and global warp parameters.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeReverseReachability

open DirectedPath Alternating AlternatingComponents

universe u

variable {V : Type u} {Gamma : DWeb V}

theorem CurrentSafeOccurrence.terminal?_transport
    {current Y : Set Gamma.DPath} {s t : V} (h : s = t)
    (A : CurrentSafeOccurrence current Y s) :
    (h ▸ A).terminal? = A.terminal? := by
  subst t
  rfl

private theorem familyEdges_mono {A B : Set Gamma.DPath} (hAB : A ⊆ B) :
    familyEdges A ⊆ familyEdges B := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  rcases he with ⟨p, hp, hep⟩
  exact ⟨p, hAB hp, hep⟩

private theorem familyEdges_pathsInComponent_subset
    (W Y A : Set Gamma.DPath) (root : V) :
    familyEdges (Alternating.pathsInComponent W Y A root) ⊆ familyEdges A :=
  familyEdges_mono fun _ hp ↦ hp.1

private theorem initialSet_mem_vertexSet {A : Set Gamma.DPath} {x : V}
    (hx : x ∈ Gamma.initialSet A) : x ∈ Gamma.vertexSet A := by
  rcases hx with ⟨p, hp, rfl⟩
  exact ⟨p, hp, p.initial_mem_support⟩

private theorem terminalFrontier_mem_vertexSet {A : Set Gamma.DPath} {x : V}
    (hx : x ∈ Gamma.terminalFrontier A) : x ∈ Gamma.vertexSet A := by
  rcases hx with ⟨p, hp, hpx⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = (.inl q : Gamma.DPath) := by
    cases p with
    | inl q => exact ⟨q, rfl⟩
    | inr r => simp at hpx
  change some q.finish = some x at hpx
  have hqx : q.finish = x := Option.some.inj hpx
  exact ⟨.inl q, hp, hqx ▸ q.finish_mem_support⟩

/-- Retype the reference parameter along an inclusion of reference edge
relations.  Vertices, colours, and actual edge occurrences are unchanged. -/
def promoteFiniteReference {current Yc Y : Set Gamma.DPath}
    (Q : FiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) :
    FiniteColouredOccurrenceWord current Y where
  length := Q.length
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases h : Q.direction i with
    | forward => simpa [h] using Q.actualEdge_spec i
    | backward =>
        exact hYY (by simpa [h] using Q.actualEdge_spec i)
  occurrence_injective := Q.occurrence_injective

@[simp] theorem promoteFiniteReference_vertex
    {current Yc Y : Set Gamma.DPath}
    (Q : FiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) (i : Fin (Q.length + 1)) :
    (promoteFiniteReference Q hYY).vertex i = Q.vertex i := rfl

@[simp] theorem promoteFiniteReference_forwardEdges
    {current Yc Y : Set Gamma.DPath}
    (Q : FiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) :
    (promoteFiniteReference Q hYY).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem promoteFiniteReference_backwardEdges
    {current Yc Y : Set Gamma.DPath}
    (Q : FiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) :
    (promoteFiniteReference Q hYY).backwardEdges = Q.backwardEdges := rfl

/-- Infinite reference-parameter promotion, with literal occurrence data
unchanged. -/
def promoteInfiniteReference {current Yc Y : Set Gamma.DPath}
    (Q : InfiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) :
    InfiniteColouredOccurrenceWord current Y where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases h : Q.direction i with
    | forward => simpa [h] using Q.actualEdge_spec i
    | backward =>
        exact hYY (by simpa [h] using Q.actualEdge_spec i)
  occurrence_injective := Q.occurrence_injective

@[simp] theorem promoteInfiniteReference_vertex
    {current Yc Y : Set Gamma.DPath}
    (Q : InfiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) (i : ℕ) :
    (promoteInfiniteReference Q hYY).vertex i = Q.vertex i := rfl

@[simp] theorem promoteInfiniteReference_forwardEdges
    {current Yc Y : Set Gamma.DPath}
    (Q : InfiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) :
    (promoteInfiniteReference Q hYY).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem promoteInfiniteReference_backwardEdges
    {current Yc Y : Set Gamma.DPath}
    (Q : InfiniteColouredOccurrenceWord current Yc)
    (hYY : familyEdges Yc ⊆ familyEdges Y) :
    (promoteInfiniteReference Q hYY).backwardEdges = Q.backwardEdges := rfl

private theorem forwardEdge_endpoints_mem_component
    {W Y current : Set Gamma.DPath} {root : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hcurrent : familyEdges current ⊆
      familyEdges (Alternating.pathsInComponent W Y W root) ∪
        familyEdges (Alternating.pathsInComponent W Y Y root))
    {e : V × V} (he : e ∈ familyEdges current) :
    e.1 ∈ component W Y root ∧ e.2 ∈ component W Y root := by
  rcases hcurrent he with heW | heY
  · have hev := familyEdges_subset_vertexSet_prod _ heW
    exact ⟨Alternating.vertexSet_pathsInComponent_left_subset hWfinite hev.1,
      Alternating.vertexSet_pathsInComponent_left_subset hWfinite hev.2⟩
  · have hev := familyEdges_subset_vertexSet_prod _ heY
    exact ⟨Alternating.vertexSet_pathsInComponent_right_subset hYfinite hev.1,
      Alternating.vertexSet_pathsInComponent_right_subset hYfinite hev.2⟩

private theorem referenceEdge_mem_componentRestriction_of_tail
    {W Y : Set Gamma.DPath} {root : V} (hYfinite : Gamma.HasFiniteCharacter Y)
    {e : V × V} (heY : e ∈ familyEdges Y)
    (heC : e.1 ∈ component W Y root) :
    e ∈ familyEdges (Alternating.pathsInComponent W Y Y root) :=
  Alternating.mem_familyEdges_pathsInComponent_right_of_mem hYfinite heY heC

private theorem referenceEdge_mem_componentRestriction_of_head
    {W Y : Set Gamma.DPath} {root : V} (hYfinite : Gamma.HasFiniteCharacter Y)
    {e : V × V} (heY : e ∈ familyEdges Y)
    (heC : e.2 ∈ component W Y root) :
    e ∈ familyEdges (Alternating.pathsInComponent W Y Y root) := by
  have htail : e.1 ∈ component W Y root :=
    component_trans heC (Relation.ReflTransGen.single (Or.inr (Or.inr heY)))
  exact referenceEdge_mem_componentRestriction_of_tail hYfinite heY htail

theorem terminalFrontier_mem_componentRestriction_right
    {W Y : Set Gamma.DPath} {root x : V}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hxY : x ∈ Gamma.terminalFrontier Y) (hxC : x ∈ component W Y root) :
    x ∈ Gamma.terminalFrontier
      (Alternating.pathsInComponent W Y Y root) := by
  rcases hxY with ⟨p, hpY, hpx⟩
  obtain ⟨q, rfl⟩ := hYfinite hpY
  change some q.finish = some x at hpx
  have hfinish : q.finish = x := Option.some.inj hpx
  have hstartC : q.start ∈ component W Y root :=
    finitePath_support_subset_component_of_touches_right hxC hpY
      (hfinish ▸ q.finish_mem_support) q.start_mem_support
  exact ⟨.inl q, ⟨hpY, hstartC⟩, hpx⟩

private theorem backwardIntersection_empty_of_outside_component
    {W Y : Set Gamma.DPath} {root : V}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    {B : Set (V × V)}
    (hB : B ⊆ familyEdges (Alternating.pathsInComponent W Y Y root))
    {p : Gamma.DPath} (hpY : p ∈ Y)
    (hpOutside : p.initial ∉ component W Y root) :
    B ∩ p.edgeSet = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨heB, hep⟩
  have heLocal := hB heB
  have heVertices := familyEdges_subset_vertexSet_prod _ heLocal
  have heC : e.1 ∈ component W Y root :=
    Alternating.vertexSet_pathsInComponent_right_subset hYfinite heVertices.1
  obtain ⟨q, rfl⟩ := hYfinite hpY
  have hes := q.edgeSet_subset_support_prod hep
  exact hpOutside
    (finitePath_support_subset_component_of_touches_right heC hpY
      hes.1 q.start_mem_support)

/-- Finite interval safeness promotes from a whole alternating component to
the full reference warp. -/
theorem finite_promoteReference_isIntervalSafe
    {W Y current : Set Gamma.DPath} {root : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hcurrent : familyEdges current ⊆
      familyEdges (Alternating.pathsInComponent W Y W root) ∪
        familyEdges (Alternating.pathsInComponent W Y Y root))
    {Q : FiniteColouredOccurrenceWord current
      (Alternating.pathsInComponent W Y Y root)} (hQ : Q.IsIntervalSafe) :
    (promoteFiniteReference Q
      (familyEdges_pathsInComponent_subset W Y Y root)).IsIntervalSafe := by
  let Yc := Alternating.pathsInComponent W Y Y root
  let hYY : familyEdges Yc ⊆ familyEdges Y :=
    familyEdges_pathsInComponent_subset W Y Y root
  have hforwardC : ∀ {e : V × V}, e ∈ Q.forwardEdges →
      e.1 ∈ component W Y root ∧ e.2 ∈ component W Y root := by
    intro e he
    exact forwardEdge_endpoints_mem_component hWfinite hYfinite hcurrent
      (Q.forwardEdges_subset_familyEdges he)
  refine {
    incoming_removed := ?_
    outgoing_removed := ?_
    intervals := ?_
    endpoint_pure := ?_ }
  · intro a b x hax hbx
    rw [promoteFiniteReference_forwardEdges] at hax
    rw [promoteFiniteReference_backwardEdges]
    exact hQ.incoming_removed hax
      (referenceEdge_mem_componentRestriction_of_head hYfinite hbx
        (hforwardC hax).2)
  · intro x a b hxa hxb
    rw [promoteFiniteReference_forwardEdges] at hxa
    rw [promoteFiniteReference_backwardEdges]
    exact hQ.outgoing_removed hxa
      (referenceEdge_mem_componentRestriction_of_tail hYfinite hxb
        (hforwardC hxa).1)
  · intro p hpY
    rw [promoteFiniteReference_backwardEdges]
    by_cases hpC : p.initial ∈ component W Y root
    · exact hQ.intervals p ⟨hpY, hpC⟩
    · exact Or.inl (backwardIntersection_empty_of_outside_component
        hYfinite Q.backwardEdges_subset_familyEdges hpY hpC)
  · intro x y hxy
    rw [promoteFiniteReference_forwardEdges] at hxy
    have hlocal := hQ.endpoint_pure hxy
    have hC := hforwardC hxy
    constructor
    · intro hyInitial
      apply hlocal.1
      rw [Alternating.initialSet_pathsInComponent]
      exact ⟨hyInitial, hC.2⟩
    · intro hxTerminal
      apply hlocal.2
      exact terminalFrontier_mem_componentRestriction_right hYfinite
        hxTerminal hC.1

/-- Infinite interval safeness promotes by the same component-closure
argument. -/
theorem infinite_promoteReference_isIntervalSafe
    {W Y current : Set Gamma.DPath} {root : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hcurrent : familyEdges current ⊆
      familyEdges (Alternating.pathsInComponent W Y W root) ∪
        familyEdges (Alternating.pathsInComponent W Y Y root))
    {Q : InfiniteColouredOccurrenceWord current
      (Alternating.pathsInComponent W Y Y root)} (hQ : Q.IsIntervalSafe) :
    (promoteInfiniteReference Q
      (familyEdges_pathsInComponent_subset W Y Y root)).IsIntervalSafe := by
  have hforwardC : ∀ {e : V × V}, e ∈ Q.forwardEdges →
      e.1 ∈ component W Y root ∧ e.2 ∈ component W Y root := by
    intro e he
    exact forwardEdge_endpoints_mem_component hWfinite hYfinite hcurrent
      (Q.forwardEdges_subset_familyEdges he)
  refine {
    incoming_removed := ?_
    outgoing_removed := ?_
    intervals := ?_
    endpoint_pure := ?_ }
  · intro a b x hax hbx
    rw [promoteInfiniteReference_forwardEdges] at hax
    rw [promoteInfiniteReference_backwardEdges]
    exact hQ.incoming_removed hax
      (referenceEdge_mem_componentRestriction_of_head hYfinite hbx
        (hforwardC hax).2)
  · intro x a b hxa hxb
    rw [promoteInfiniteReference_forwardEdges] at hxa
    rw [promoteInfiniteReference_backwardEdges]
    exact hQ.outgoing_removed hxa
      (referenceEdge_mem_componentRestriction_of_tail hYfinite hxb
        (hforwardC hxa).1)
  · intro p hpY
    rw [promoteInfiniteReference_backwardEdges]
    by_cases hpC : p.initial ∈ component W Y root
    · exact hQ.intervals p ⟨hpY, hpC⟩
    · exact Or.inl (backwardIntersection_empty_of_outside_component
        hYfinite Q.backwardEdges_subset_familyEdges hpY hpC)
  · intro x y hxy
    rw [promoteInfiniteReference_forwardEdges] at hxy
    have hlocal := hQ.endpoint_pure hxy
    have hC := hforwardC hxy
    constructor
    · intro hyInitial
      apply hlocal.1
      rw [Alternating.initialSet_pathsInComponent]
      exact ⟨hyInitial, hC.2⟩
    · intro hxTerminal
      apply hlocal.2
      exact terminalFrontier_mem_componentRestriction_right hYfinite
        hxTerminal hC.1

/-- Promote either shape of current-warp occurrence while retaining the
literal word and its actual birth-stage forward warp. -/
def promoteComponentOccurrence
    {W Y current : Set Gamma.DPath} {root s : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hcurrent : familyEdges current ⊆
      familyEdges (Alternating.pathsInComponent W Y W root) ∪
        familyEdges (Alternating.pathsInComponent W Y Y root))
    (A : CurrentSafeOccurrence current
      (Alternating.pathsInComponent W Y Y root) s) :
    CurrentSafeOccurrence current Y s := by
  cases A with
  | infinite Q hsafe hfirst =>
      exact .infinite
        (promoteInfiniteReference Q
          (familyEdges_pathsInComponent_subset W Y Y root))
        (infinite_promoteReference_isIntervalSafe hWfinite hYfinite
          hcurrent hsafe) hfirst
  | finite t Q hsafe hfirst hlast =>
      exact .finite t
        (promoteFiniteReference Q
          (familyEdges_pathsInComponent_subset W Y Y root))
        (finite_promoteReference_isIntervalSafe hWfinite hYfinite
          hcurrent hsafe) hfirst hlast

@[simp] theorem promoteComponentOccurrence_terminal?
    {W Y current : Set Gamma.DPath} {root s : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hcurrent : familyEdges current ⊆
      familyEdges (Alternating.pathsInComponent W Y W root) ∪
        familyEdges (Alternating.pathsInComponent W Y Y root))
    (A : CurrentSafeOccurrence current
      (Alternating.pathsInComponent W Y Y root) s) :
    (promoteComponentOccurrence hWfinite hYfinite hcurrent A).terminal? =
      A.terminal? := by
  cases A <;> rfl

/-- Promote one local assigned datum to the original pair.  The current warp
remains the honest local birth-stage warp; only the reference parameter is
promoted. -/
def promoteComponentAssignedData
    {W Y : Set Gamma.DPath} {root : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (s : UncoveredInitial W Y)
    (sc : UncoveredInitial
      (Alternating.pathsInComponent W Y W root)
      (Alternating.pathsInComponent W Y Y root))
    (hsc : sc.1 = s.1)
    (D : WeakAssignedData
      (Alternating.pathsInComponent W Y W root)
      (Alternating.pathsInComponent W Y Y root) sc) :
    WeakAssignedData W Y s := by
  let occurrenceLocal : CurrentSafeOccurrence D.current
      (Alternating.pathsInComponent W Y Y root) s.1 := hsc ▸ D.occurrence
  let occurrenceGlobal : CurrentSafeOccurrence D.current Y s.1 :=
    promoteComponentOccurrence hWfinite hYfinite D.current_edges occurrenceLocal
  refine {
    current := D.current
    current_isWarp := D.current_isWarp
    current_finite := D.current_finite
    current_edges := ?_
    current_initial_subset := ?_
    current_terminal_subset := ?_
    occurrence := occurrenceGlobal
    finite_terminal_original := ?_ }
  · intro e he
    rcases D.current_edges he with heW | heY
    · exact Or.inl ((familyEdges_pathsInComponent_subset W Y W root) heW)
    · exact Or.inr ((familyEdges_pathsInComponent_subset W Y Y root) heY)
  · exact D.current_initial_subset.trans (by
      intro x hx
      rw [Alternating.initialSet_pathsInComponent] at hx
      exact hx.1)
  · exact D.current_terminal_subset.trans
      (Alternating.terminalFrontier_pathsInComponent_subset W Y W root)
  · intro t ht
    have htOccurrenceLocal : occurrenceLocal.terminal? = some t := by
      simpa [occurrenceGlobal] using ht
    have htLocalTerminal : D.occurrence.terminal? = some t := by
      rw [← CurrentSafeOccurrence.terminal?_transport hsc D.occurrence]
      exact htOccurrenceLocal
    have htLocal := D.finite_terminal_original htLocalTerminal
    refine ⟨Alternating.terminalFrontier_pathsInComponent_subset W Y W root
      htLocal.1, ?_⟩
    intro htY
    apply htLocal.2
    rw [Alternating.vertexSet_pathsInComponent_right hYfinite]
    have htWC := htLocal.1
    rw [Alternating.terminalFrontier_pathsInComponent_left hWfinite] at htWC
    exact ⟨htY, htWC.2⟩

@[simp] theorem promoteComponentAssignedData_terminal?
    {W Y : Set Gamma.DPath} {root : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (s : UncoveredInitial W Y)
    (sc : UncoveredInitial
      (Alternating.pathsInComponent W Y W root)
      (Alternating.pathsInComponent W Y Y root))
    (hsc : sc.1 = s.1)
    (D : WeakAssignedData
      (Alternating.pathsInComponent W Y W root)
      (Alternating.pathsInComponent W Y Y root) sc) :
    (promoteComponentAssignedData hWfinite hYfinite s sc hsc D).occurrence.terminal? =
      D.occurrence.terminal? := by
  let occurrenceLocal : CurrentSafeOccurrence D.current
      (Alternating.pathsInComponent W Y Y root) s.1 := hsc ▸ D.occurrence
  change (promoteComponentOccurrence hWfinite hYfinite D.current_edges
    occurrenceLocal).terminal? = D.occurrence.terminal?
  rw [promoteComponentOccurrence_terminal?]
  exact CurrentSafeOccurrence.terminal?_transport hsc D.occurrence

theorem promoteComponentAssignedData_finite_terminal_mem_component
    {W Y : Set Gamma.DPath} {root : V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (s : UncoveredInitial W Y)
    (sc : UncoveredInitial
      (Alternating.pathsInComponent W Y W root)
      (Alternating.pathsInComponent W Y Y root))
    (hsc : sc.1 = s.1)
    (D : WeakAssignedData
      (Alternating.pathsInComponent W Y W root)
      (Alternating.pathsInComponent W Y Y root) sc)
    {t : V}
    (ht : (promoteComponentAssignedData hWfinite hYfinite s sc hsc D).occurrence.terminal? =
      some t) :
    t ∈ component W Y root := by
  let occurrenceLocal : CurrentSafeOccurrence D.current
      (Alternating.pathsInComponent W Y Y root) s.1 := hsc ▸ D.occurrence
  have htOccurrenceLocal : occurrenceLocal.terminal? = some t := by
    change (promoteComponentOccurrence hWfinite hYfinite D.current_edges
      occurrenceLocal).terminal? = some t at ht
    rwa [promoteComponentOccurrence_terminal?] at ht
  have htLocalTerminal : D.occurrence.terminal? = some t := by
    rw [← CurrentSafeOccurrence.terminal?_transport hsc D.occurrence]
    exact htOccurrenceLocal
  have htWc := (D.finite_terminal_original htLocalTerminal).1
  rw [Alternating.terminalFrontier_pathsInComponent_left hWfinite] at htWc
  exact htWc.2

#print axioms finite_promoteReference_isIntervalSafe
#print axioms infinite_promoteReference_isIntervalSafe
#print axioms promoteComponentAssignedData
#print axioms promoteComponentAssignedData_terminal?
#print axioms promoteComponentAssignedData_finite_terminal_mem_component

end Erdos599.ColouredSafeReverseReachability
