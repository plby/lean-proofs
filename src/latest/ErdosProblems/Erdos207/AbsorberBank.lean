/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberTransport

/-!
# Switching a finite bank of exclusive absorbers

An exclusive absorber has two decompositions: the out-side decomposes its
private graph, while the in-side decomposes that graph together with its root.
This file proves the exact finite gluing statement used by the KSSS cycle
cover. If the extended graphs of the attached gadgets are pairwise
edge-disjoint, then every chosen subset of roots can be absorbed
simultaneously.
-/

namespace Erdos207

open Finset

/-- The supremum of a finite indexed family of graphs. -/
def graphSup {I V : Type*} [DecidableEq I]
    (s : Finset I) (G : I → SimpleGraph V) : SimpleGraph V :=
  s.sup G

/-- The union of a finite indexed family of triple systems. -/
def tripleUnion {I V : Type*} [DecidableEq I] [DecidableEq V]
    (s : Finset I) (C : I → TripleSystemOn V) : TripleSystemOn V :=
  s.biUnion C

@[simp]
lemma graphSup_empty {I V : Type*} [DecidableEq I]
    (G : I → SimpleGraph V) : graphSup ∅ G = ⊥ := by
  simp [graphSup]

@[simp]
lemma graphSup_insert {I V : Type*} [DecidableEq I]
    (i : I) (s : Finset I) (G : I → SimpleGraph V) :
    graphSup (insert i s) G = G i ⊔ graphSup s G := by
  simp [graphSup]

@[simp]
lemma tripleUnion_empty {I V : Type*} [DecidableEq I] [DecidableEq V]
    (C : I → TripleSystemOn V) : tripleUnion ∅ C = ∅ := by
  simp [tripleUnion]

@[simp]
lemma tripleUnion_insert {I V : Type*} [DecidableEq I] [DecidableEq V]
    (i : I) (s : Finset I) (C : I → TripleSystemOn V) :
    tripleUnion (insert i s) C = C i ∪ tripleUnion s C := by
  simp [tripleUnion]

/-- One member of a pairwise edge-disjoint family is disjoint from the
supremum of all the other members in a finite index set. -/
lemma disjoint_graphSup_of_pairwise
    {I V : Type*} [DecidableEq I] (i : I) (s : Finset I)
    (G : I → SimpleGraph V)
    (h : ∀ j ∈ s, Disjoint (G i) (G j)) :
    Disjoint (G i) (graphSup s G) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [graphSup_insert, disjoint_sup_right]
      exact ⟨h j (mem_insert_self j s), ih fun k hk ↦
        h k (mem_insert_of_mem hk)⟩

/-- Finitely many decompositions of pairwise edge-disjoint graphs glue to a
decomposition of their graph supremum. -/
theorem triangleDecomposition_graphSup_tripleUnion
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (s : Finset I) (G : I → SimpleGraph V)
    (C : I → TripleSystemOn V)
    (hdec : ∀ i ∈ s, IsTriangleDecomposition (G i) (C i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (G i) (G j)) :
    IsTriangleDecomposition (graphSup s G) (tripleUnion s C) := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [graphSup_empty, tripleUnion_empty]
      constructor
      · intro T hT
        simp at hT
      · intro u v huv
        simpa using huv
  | @insert i s his ih =>
      rw [graphSup_insert, tripleUnion_insert]
      apply (hdec i (mem_insert_self i s)).union
      · apply ih
        · intro j hj
          exact hdec j (mem_insert_of_mem hj)
        · intro j hj k hk hjk
          exact hdisj j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hjk
      · apply disjoint_graphSup_of_pairwise
        intro j hj
        exact hdisj i (mem_insert_self i s) j (mem_insert_of_mem hj) fun hij ↦
          his (hij ▸ hj)

/-- The graph decomposed by one absorber after deciding whether to switch it
to its in-side. -/
def switchedAbsorberGraph {I V : Type*} [DecidableEq I] [DecidableEq V]
    (selected : Finset I) (root : I → SimpleGraph V)
    (out : I → TripleSystemOn V) (i : I) : SimpleGraph V :=
  coveredGraph (out i) ⊔ if i ∈ selected then root i else ⊥

/-- The triple family used by one absorber after deciding whether to switch
it to its in-side. -/
def switchedAbsorberTriples {I V : Type*} [DecidableEq I] [DecidableEq V]
    (selected : Finset I) (out inn : I → TripleSystemOn V) (i : I) :
    TripleSystemOn V :=
  if i ∈ selected then inn i else out i

/-- Separating the fixed out-graphs from the roots that were switched in. -/
lemma graphSup_switchedAbsorberGraph
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (s selected : Finset I) (root : I → SimpleGraph V)
    (out : I → TripleSystemOn V) :
    graphSup s (switchedAbsorberGraph selected root out) =
      graphSup s (fun i => coveredGraph (out i)) ⊔
        graphSup (selected ∩ s) root := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      by_cases hsel : i ∈ selected
      · simp [hsel, ih, switchedAbsorberGraph]
        ac_rfl
      · simp [hsel, ih, switchedAbsorberGraph]
        ac_rfl

lemma graphSup_univ_switchedAbsorberGraph
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (selected : Finset I) (root : I → SimpleGraph V)
    (out : I → TripleSystemOn V) :
    graphSup univ (switchedAbsorberGraph selected root out) =
      graphSup univ (fun i => coveredGraph (out i)) ⊔
        graphSup selected root := by
  rw [graphSup_switchedAbsorberGraph]
  simp

/-- Exact simultaneous switching theorem for a bank of exclusive graph
absorbers. Pairwise disjointness is required only for each gadget's largest
possible graph, namely its out-graph together with its root. -/
theorem exclusiveAbsorberBank_switch
    {I V : Type*} [DecidableEq I] [Fintype V] [DecidableEq V]
    (s selected : Finset I) (root : I → SimpleGraph V)
    (out inn : I → TripleSystemOn V)
    (habs : ∀ i ∈ s, IsExclusiveGraphAbsorberOn (root i) (out i) (inn i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (coveredGraph (out i) ⊔ root i)
        (coveredGraph (out j) ⊔ root j)) :
    IsTriangleDecomposition
      (graphSup s (switchedAbsorberGraph selected root out))
      (tripleUnion s (switchedAbsorberTriples selected out inn)) := by
  apply triangleDecomposition_graphSup_tripleUnion
  · intro i hi
    by_cases hisel : i ∈ selected
    · simp only [switchedAbsorberGraph, switchedAbsorberTriples, hisel,
        if_true]
      exact (habs i hi).in_decomposition
    · simp only [switchedAbsorberGraph, switchedAbsorberTriples, hisel,
        if_false, sup_bot_eq]
      exact (habs i hi).out_decomposition
  · intro i hi j hj hij
    apply (hdisj i hi j hj hij).mono
    · unfold switchedAbsorberGraph
      split <;> simp
    · unfold switchedAbsorberGraph
      split <;> simp

/-- Variant of `exclusiveAbsorberBank_switch` with the exact disjointness
hypothesis needed in the universal cycle-cover bank.  Unused copies contribute
only their out-graphs, so their overlapping *potential* root graphs are
irrelevant. -/
theorem exclusiveAbsorberBank_switch_of_switched_disjoint
    {I V : Type*} [DecidableEq I] [Fintype V] [DecidableEq V]
    (s selected : Finset I) (root : I → SimpleGraph V)
    (out inn : I → TripleSystemOn V)
    (habs : ∀ i ∈ s, IsExclusiveGraphAbsorberOn (root i) (out i) (inn i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (switchedAbsorberGraph selected root out i)
        (switchedAbsorberGraph selected root out j)) :
    IsTriangleDecomposition
      (graphSup s (switchedAbsorberGraph selected root out))
      (tripleUnion s (switchedAbsorberTriples selected out inn)) := by
  apply triangleDecomposition_graphSup_tripleUnion
  · intro i hi
    by_cases hisel : i ∈ selected
    · simp only [switchedAbsorberGraph, switchedAbsorberTriples, hisel,
        if_true]
      exact (habs i hi).in_decomposition
    · simp only [switchedAbsorberGraph, switchedAbsorberTriples, hisel,
        if_false, sup_bot_eq]
      exact (habs i hi).out_decomposition
  · exact hdisj

end Erdos207
