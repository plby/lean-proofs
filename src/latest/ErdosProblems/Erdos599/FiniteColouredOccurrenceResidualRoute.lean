/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceCertifiedReduction
import ErdosProblems.Erdos599.FiniteColouredOccurrenceContraction
import ErdosProblems.Erdos599.SafeSwitchingAssembly
import ErdosProblems.Erdos599.TwoWarpMatchingProjection

/-!
# The occurrence route carried by a residual reduction path

A residual-port path is directed from the terminal receiving port back to
the source sending port.  Reversing it, deleting exactly the diagonal
completion steps, and forgetting the port copies gives a finite coloured
occurrence word in the original forward and reference families.

This construction retains the chronological path, not only its boundary
balance.  Its forward edges are exactly the old-family edges deleted by the
reduction, while its backward edges are exactly the reference edges inserted
by the reduction.  No interval-safeness assertion is made: that is precisely
the nonlocal content needed by a later source-changing exchange.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath
open TwoWarpMatchingTraversal
open ColouredResidualPortContinuation ColouredResidualPortReduction

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

private def pathVertex {U : Type u} {D : Digraph U}
    (p : FinitePath D) : Fin (p.walk.length + 1) → U := fun i ↦
  p.walk.support.get (Fin.cast (Walk.support_length_eq p.walk).symm i)

@[simp] private theorem pathVertex_zero {U : Type u} {D : Digraph U}
    (p : FinitePath D) : pathVertex p 0 = p.start := by
  simpa [pathVertex] using p.support_getElem_zero

@[simp] private theorem pathVertex_last {U : Type u} {D : Digraph U}
    (p : FinitePath D) :
    pathVertex p (Fin.last p.walk.length) = p.finish := by
  simpa [pathVertex] using Walk.getElem_length_eq_end p.walk

private theorem pathVertex_injective {U : Type u} {D : Digraph U}
    (p : FinitePath D) : Function.Injective (pathVertex p) := by
  intro i j hij
  apply Fin.ext
  have hcast := p.isPath.injective_get hij
  simpa [pathVertex] using congrArg Fin.val hcast

private theorem pathVertex_edge_mem {U : Type u} {D : Digraph U}
    (p : FinitePath D) (i : Fin p.walk.length) :
    (pathVertex p i.castSucc, pathVertex p i.succ) ∈ p.edgeSet := by
  rw [FinitePath.edgeSet, Walk.mem_edgeSet_iff_exists_getVert]
  refine ⟨i.1, i.2, ?_, ?_⟩
  · rw [Walk.support_length_eq]
    omega
  · simp only [pathVertex]
    congr 1 <;> apply Fin.ext <;> simp

private abbrev reverseVertex
    (P : FinitePath (residualPortDigraph W Y)) := pathVertex P.reverse

private abbrev retainedSteps
    (P : FinitePath (residualPortDigraph W Y)) :=
  ConnectorDeletion.properSteps (reverseVertex P) projectPort

private abbrev retainedIndex
    (P : FinitePath (residualPortDigraph W Y)) :=
  ConnectorDeletion.properIndex (reverseVertex P) projectPort

/-- The colour of a non-diagonal step in the reversed residual path. -/
private def residualRouteDirection
    (P : FinitePath (residualPortDigraph W Y))
    (j : Fin (retainedSteps P).card) : Direction :=
  match reverseVertex P (retainedIndex P j).castSucc with
  | .inl _ => .forward
  | .inr _ => .backward

private abbrev residualRouteVertex
    (P : FinitePath (residualPortDigraph W Y)) :=
  ConnectorDeletion.vertex (reverseVertex P) projectPort

/-- A retained reversed residual edge is either an old-family edge traversed
forward or a reference edge traversed backward. -/
private theorem retainedEdge_cases
    (P : FinitePath (residualPortDigraph W Y))
    (j : Fin (retainedSteps P).card) :
    let i := retainedIndex P j
    let a := reverseVertex P i.castSucc
    let b := reverseVertex P i.succ
    (∃ x y, a = .inl x ∧ b = .inr y ∧ (x, y) ∈ familyEdges W) ∨
      ∃ x y, a = .inr y ∧ b = .inl x ∧ (x, y) ∈ familyEdges Y := by
  let i := retainedIndex P j
  let a := reverseVertex P i.castSucc
  let b := reverseVertex P i.succ
  have hiProper : i ∈ retainedSteps P := ConnectorDeletion.properIndex_mem _ _ j
  have hne : projectPort a ≠ projectPort b := by
    simpa [retainedSteps, i, a, b] using
      (ConnectorDeletion.mem_properSteps (reverseVertex P) projectPort i).mp
        hiProper
  have hrev : (a, b) ∈ P.reverse.edgeSet := by
    simpa [i, a, b] using pathVertex_edge_mem P.reverse i
  have horig : (b, a) ∈ P.edgeSet :=
    (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff P).mp hrev
  have hadj := P.edgeSet_subset_adj horig
  rcases ha : a with x | y <;> rcases hb : b with x' | y' <;>
      simp only [ha, hb, residualPortDigraph, ResidualStep, projectPort] at hadj hne
  · exact False.elim hadj
  · rcases hadj with hW | hidentity
    · exact Or.inl ⟨x, y', ha, hb, hW⟩
    · exact False.elim (hne hidentity.1)
  · rcases hadj.1 with hY | hidentity
    · exact Or.inr ⟨x', y, ha, hb, hY⟩
    · exact False.elim (hne hidentity.symm)
  · exact False.elim hadj

private theorem retainedEdge_direction_and_spec
    (P : FinitePath (residualPortDigraph W Y))
    (j : Fin (retainedSteps P).card) :
    let i := retainedIndex P j
    let a := reverseVertex P i.castSucc
    let b := reverseVertex P i.succ
    match residualRouteDirection P j with
    | .forward => (projectPort a, projectPort b) ∈ familyEdges W
    | .backward => (projectPort b, projectPort a) ∈ familyEdges Y := by
  rcases retainedEdge_cases P j with
    ⟨x, y, ha, hb, hW⟩ | ⟨x, y, ha, hb, hY⟩
  · simpa [residualRouteDirection, ha, hb, projectPort] using hW
  · simpa [residualRouteDirection, ha, hb, projectPort] using hY

private def residualRouteData
    (P : FinitePath (residualPortDigraph W Y))
    (j : Fin (retainedSteps P).card) : Direction × (V × V) :=
  (residualRouteDirection P j,
    match residualRouteDirection P j with
    | .forward =>
        (residualRouteVertex P j.castSucc, residualRouteVertex P j.succ)
    | .backward =>
        (residualRouteVertex P j.succ, residualRouteVertex P j.castSucc))

private theorem residualRouteData_injective
    (P : FinitePath (residualPortDigraph W Y)) :
    Function.Injective (residualRouteData P) := by
  intro j k hjk
  rcases retainedEdge_cases P j with
    ⟨x, y, hja, hjb, _hjW⟩ | ⟨x, y, hja, hjb, _hjY⟩ <;>
    rcases retainedEdge_cases P k with
      ⟨x', y', hka, hkb, _hkW⟩ | ⟨x', y', hka, hkb, _hkY⟩
  · have hedge : (x, y) = (x', y') := by
      have h := congrArg Prod.snd hjk
      simpa [residualRouteData, residualRouteDirection,
        residualRouteVertex, ConnectorDeletion.vertex_castSucc,
        ConnectorDeletion.vertex_succ, hja, hjb, hka, hkb, projectPort] using h
    have hsource :
        reverseVertex P (retainedIndex P j).castSucc =
          reverseVertex P (retainedIndex P k).castSucc := by
      calc
        _ = .inl x := hja
        _ = .inl x' := congrArg Sum.inl (congrArg Prod.fst hedge)
        _ = _ := hka.symm
    have hindexCast := pathVertex_injective P.reverse hsource
    have hindex : retainedIndex P j = retainedIndex P k :=
      Fin.castSucc_inj.mp hindexCast
    exact (retainedIndex P).injective hindex
  · have h := congrArg Prod.fst hjk
    simp [residualRouteData, residualRouteDirection, hja, hka] at h
  · have h := congrArg Prod.fst hjk
    simp [residualRouteData, residualRouteDirection, hja, hka] at h
  · have hedge : (x, y) = (x', y') := by
      have h := congrArg Prod.snd hjk
      simpa [residualRouteData, residualRouteDirection,
        residualRouteVertex, ConnectorDeletion.vertex_castSucc,
        ConnectorDeletion.vertex_succ, hja, hjb, hka, hkb, projectPort] using h
    have hsource :
        reverseVertex P (retainedIndex P j).castSucc =
          reverseVertex P (retainedIndex P k).castSucc := by
      calc
        _ = .inr y := hja
        _ = .inr y' := congrArg Sum.inr (congrArg Prod.snd hedge)
        _ = _ := hka.symm
    have hindexCast := pathVertex_injective P.reverse hsource
    have hindex : retainedIndex P j = retainedIndex P k :=
      Fin.castSucc_inj.mp hindexCast
    exact (retainedIndex P).injective hindex

/-- Reverse a residual reduction path and delete its matching-completion
diagonals.  The result is an actual coloured occurrence word in the original
forward family and the reference family. -/
def ofResidualReductionPath
    (P : FinitePath (residualPortDigraph W Y)) :
    FiniteColouredOccurrenceWord W Y where
  length := (retainedSteps P).card
  vertex := residualRouteVertex P
  direction := residualRouteDirection P
  actualEdge_spec := by
    intro j
    rcases retainedEdge_cases P j with
      ⟨x, y, ha, hb, hW⟩ | ⟨x, y, ha, hb, hY⟩
    · simpa [residualRouteDirection, residualRouteVertex, retainedIndex,
        ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ,
        ha, hb, projectPort] using hW
    · simpa [residualRouteDirection, residualRouteVertex, retainedIndex,
        ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ,
        ha, hb, projectPort] using hY
  occurrence_injective := residualRouteData_injective P

@[simp] theorem ofResidualReductionPath_first
    (P : FinitePath (residualPortDigraph W Y)) :
    (ofResidualReductionPath P).vertex 0 = projectPort P.finish := by
  change ConnectorDeletion.vertex (reverseVertex P) projectPort 0 =
    projectPort P.reverse.start
  rw [ConnectorDeletion.vertex_first]
  simp [reverseVertex]

@[simp] theorem ofResidualReductionPath_last
    (P : FinitePath (residualPortDigraph W Y)) :
    (ofResidualReductionPath P).vertex
      (Fin.last (ofResidualReductionPath P).length) = projectPort P.start := by
  change ConnectorDeletion.vertex (reverseVertex P) projectPort
    (Fin.last (retainedSteps P).card) = projectPort P.reverse.finish
  rw [ConnectorDeletion.vertex_last]
  simp [reverseVertex]

private theorem retainedOriginalEdge
    (P : FinitePath (residualPortDigraph W Y))
    (j : Fin (retainedSteps P).card) :
    (reverseVertex P (retainedIndex P j).succ,
      reverseVertex P (retainedIndex P j).castSucc) ∈ P.edgeSet := by
  apply (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff P).mp
  exact pathVertex_edge_mem P.reverse (retainedIndex P j)

private theorem exists_retainedIndex_of_mem_reverseEdge
    (P : FinitePath (residualPortDigraph W Y)) {a b : Port V}
    (hab : (a, b) ∈ P.reverse.edgeSet)
    (hne : projectPort a ≠ projectPort b) :
    ∃ j : Fin (retainedSteps P).card,
      reverseVertex P (retainedIndex P j).castSucc = a ∧
        reverseVertex P (retainedIndex P j).succ = b := by
  rw [FinitePath.edgeSet, Walk.mem_edgeSet_iff_exists_getVert] at hab
  rcases hab with ⟨n, hn, hn', hab⟩
  let i : Fin P.reverse.walk.length := ⟨n, hn⟩
  have hpair :
      (reverseVertex P i.castSucc, reverseVertex P i.succ) = (a, b) := by
    exact Prod.ext (congrArg Prod.fst hab).symm (congrArg Prod.snd hab).symm
  have hiProper : i ∈ retainedSteps P := by
    rw [ConnectorDeletion.mem_properSteps]
    intro heq
    apply hne
    calc
      projectPort a = projectPort (reverseVertex P i.castSucc) :=
        congrArg projectPort (congrArg Prod.fst hpair).symm
      _ = projectPort (reverseVertex P i.succ) := heq
      _ = projectPort b := congrArg projectPort (congrArg Prod.snd hpair)
  obtain ⟨j, hj⟩ := ConnectorDeletion.exists_properIndex
    (reverseVertex P) projectPort hiProper
  refine ⟨j, ?_, ?_⟩
  · rw [hj]
    exact congrArg Prod.fst hpair
  · rw [hj]
    exact congrArg Prod.snd hpair

theorem ofResidualReductionPath_forwardEdges_subset_backwardEdges
    (P : FinitePath (residualPortDigraph W Y)) :
    (ofResidualReductionPath P).forwardEdges ⊆
      ColouredResidualPortReduction.backwardEdges P := by
  rintro e ⟨j, rfl⟩
  rcases retainedEdge_cases P j.1 with
    ⟨x, y, ha, hb, hW⟩ | ⟨x, y, ha, hb, _hY⟩
  · have hEdge : (Sum.inr y, Sum.inl x) ∈ P.edgeSet := by
      simpa [ha, hb] using retainedOriginalEdge P j.1
    have hne : x ≠ y := by
      intro hxy
      subst y
      exact not_self_mem_familyEdges W x hW
    have hrouteEdge :
        (ofResidualReductionPath P).forwardEdge j = (x, y) := by
      simp [FiniteColouredOccurrenceWord.forwardEdge,
      FiniteColouredOccurrenceWord.actualEdge, ofResidualReductionPath,
      residualRouteDirection, residualRouteVertex, retainedIndex,
      ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ,
      ha, hb, projectPort]
    rw [hrouteEdge]
    refine ⟨?_, hne⟩
    simpa [fullBackwardEdges, backwardPortEdge] using hEdge
  · have hforward :
        residualRouteDirection P j.1 = .forward := j.2
    simp [residualRouteDirection, ha] at hforward

theorem ofResidualReductionPath_backwardEdges_subset_forwardEdges
    (P : FinitePath (residualPortDigraph W Y)) :
    (ofResidualReductionPath P).backwardEdges ⊆
      ColouredResidualPortReduction.forwardEdges P := by
  rintro e ⟨j, rfl⟩
  rcases retainedEdge_cases P j.1 with
    ⟨x, y, ha, hb, _hW⟩ | ⟨x, y, ha, hb, hY⟩
  · have hbackward := (ofResidualReductionPath P).backwardIndex_direction j
    simp [ofResidualReductionPath, residualRouteDirection, ha] at hbackward
  · have hEdge : (Sum.inl x, Sum.inr y) ∈ P.edgeSet := by
      simpa [ha, hb] using retainedOriginalEdge P j.1
    have hne : x ≠ y := by
      intro hxy
      subst y
      exact not_self_mem_familyEdges Y x hY
    have hrouteEdge :
        (ofResidualReductionPath P).backwardEdge j = (x, y) := by
      simp [FiniteColouredOccurrenceWord.backwardEdge,
      FiniteColouredOccurrenceWord.actualEdge, ofResidualReductionPath,
      residualRouteDirection, residualRouteVertex, retainedIndex,
      ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ,
      ha, hb, projectPort]
    rw [hrouteEdge]
    refine ⟨?_, hne⟩
    simpa [fullForwardEdges, forwardPortEdge] using hEdge

theorem backwardEdges_subset_ofResidualReductionPath_forwardEdges
    (P : FinitePath (residualPortDigraph W Y)) :
    ColouredResidualPortReduction.backwardEdges P ⊆
      (ofResidualReductionPath P).forwardEdges := by
  rintro ⟨x, y⟩ ⟨hP, hne⟩
  have hrev : (Sum.inl x, Sum.inr y) ∈ P.reverse.edgeSet :=
    (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff P).mpr hP
  obtain ⟨j, ha, hb⟩ := exists_retainedIndex_of_mem_reverseEdge P hrev hne
  have hdir : residualRouteDirection P j = .forward := by
    simp [residualRouteDirection, ha]
  let ji : (ofResidualReductionPath P).ForwardIndex := ⟨j, hdir⟩
  refine ⟨ji, ?_⟩
  simp [ji, FiniteColouredOccurrenceWord.forwardEdge,
    FiniteColouredOccurrenceWord.actualEdge, ofResidualReductionPath,
    residualRouteDirection, residualRouteVertex, retainedIndex,
    ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ,
    ha, hb, projectPort]

theorem forwardEdges_subset_ofResidualReductionPath_backwardEdges
    (P : FinitePath (residualPortDigraph W Y)) :
    ColouredResidualPortReduction.forwardEdges P ⊆
      (ofResidualReductionPath P).backwardEdges := by
  rintro ⟨x, y⟩ ⟨hP, hne⟩
  have hrev : (Sum.inr y, Sum.inl x) ∈ P.reverse.edgeSet :=
    (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff P).mpr hP
  obtain ⟨j, ha, hb⟩ := exists_retainedIndex_of_mem_reverseEdge P hrev hne.symm
  have hdir : residualRouteDirection P j = .backward := by
    simp [residualRouteDirection, ha]
  let ji : (ofResidualReductionPath P).BackwardIndex := ⟨j, by
    intro hjf
    change residualRouteDirection P j = .forward at hjf
    rw [hdir] at hjf
    exact Direction.noConfusion hjf⟩
  refine ⟨ji, ?_⟩
  simp [ji, FiniteColouredOccurrenceWord.backwardEdge,
    FiniteColouredOccurrenceWord.actualEdge, ofResidualReductionPath,
    residualRouteDirection, residualRouteVertex, retainedIndex,
    ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ,
    ha, hb, projectPort]

theorem ofResidualReductionPath_forwardEdges
    (P : FinitePath (residualPortDigraph W Y)) :
    (ofResidualReductionPath P).forwardEdges =
      ColouredResidualPortReduction.backwardEdges P :=
  Set.Subset.antisymm
    (ofResidualReductionPath_forwardEdges_subset_backwardEdges P)
    (backwardEdges_subset_ofResidualReductionPath_forwardEdges P)

theorem ofResidualReductionPath_backwardEdges
    (P : FinitePath (residualPortDigraph W Y)) :
    (ofResidualReductionPath P).backwardEdges =
      ColouredResidualPortReduction.forwardEdges P :=
  Set.Subset.antisymm
    (ofResidualReductionPath_backwardEdges_subset_forwardEdges P)
    (forwardEdges_subset_ofResidualReductionPath_backwardEdges P)

variable {U : Set Gamma.DPath}

/-- A later word in the actual reduced warp has no forward edge in common
with the raw reverse route's forward colour.  The latter consists of exactly
the old edges deleted by the reduction. -/
theorem ofResidualReductionPath_forwardEdges_disjoint_later
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y)
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges P) ∪
        ColouredResidualPortReduction.forwardEdges P) :
    Disjoint (ofResidualReductionPath P).forwardEdges Q.forwardEdges := by
  rw [ofResidualReductionPath_forwardEdges, Set.disjoint_left]
  intro e heDeleted heQ
  rcases hUE (Q.forwardEdges_subset_familyEdges heQ) with heOld | heInserted
  · exact heOld.2 heDeleted
  · exact Set.disjoint_left.1
      (ColouredResidualPortReduction.forwardEdges_disjoint_familyEdges P)
      heInserted
      (ColouredResidualPortReduction.backwardEdges_subset_familyEdges P
        heDeleted)

/-- The inherited-edge measure is literally the opposite-colour overlap of
the later word with the ordered raw residual route. -/
theorem residualPathInheritedEdges_eq_forward_inter_routeBackward
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y) :
    residualPathInheritedEdges P Q =
      Q.forwardEdges ∩ (ofResidualReductionPath P).backwardEdges := by
  rw [ofResidualReductionPath_backwardEdges]
  rfl

/-- Ordered form of the hard reduction-transfer branch.  The inherited
edge is exhibited at its later-word forward and backward occurrences and at
the raw residual route's backward occurrence.  These are the three literal
cuts used by a source-changing cross-splice. -/
theorem residualReduction_original_or_orderedPathPivot
    (P : FinitePath (residualPortDigraph W Y))
    {Q : FiniteColouredOccurrenceWord U Y} (hQ : Q.IsIntervalSafe)
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges P) ∪
        ColouredResidualPortReduction.forwardEdges P) :
    Q.forwardEdges ⊆ familyEdges W ∨
      ∃ (e : V × V) (i j : Fin Q.length)
          (k : (ofResidualReductionPath P).BackwardIndex),
        e ∈ ColouredResidualPortReduction.forwardEdges P ∧
          e ∉ familyEdges W ∧ e ∈ familyEdges Y ∧
          Q.direction i = .forward ∧ Q.direction j = .backward ∧
          Q.actualEdge i = e ∧ Q.actualEdge j = e ∧
          (ofResidualReductionPath P).backwardEdge k = e ∧ i ≠ j := by
  rcases residualReduction_original_or_pathPivot P hQ hUE with
    hOriginal | ⟨e, i, j, heP, heW, heY, hi, hj, hie, hje, hij⟩
  · exact Or.inl hOriginal
  · have heRoute : e ∈ (ofResidualReductionPath P).backwardEdges := by
      rw [ofResidualReductionPath_backwardEdges]
      exact heP
    rcases heRoute with ⟨k, hk⟩
    exact Or.inr ⟨e, i, j, k, heP, heW, heY, hi, hj, hie, hje, hk, hij⟩

#print axioms ofResidualReductionPath
#print axioms ofResidualReductionPath_forwardEdges
#print axioms ofResidualReductionPath_backwardEdges
#print axioms ofResidualReductionPath_forwardEdges_disjoint_later
#print axioms residualReduction_original_or_orderedPathPivot

end Erdos599.Alternating.FiniteColouredOccurrenceWord
