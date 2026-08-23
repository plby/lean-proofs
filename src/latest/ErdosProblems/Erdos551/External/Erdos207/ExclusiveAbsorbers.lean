/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.Prefix
import Mathlib.Tactic.FinCases

/-!
# Explicit exclusive absorbers for the KSSS cycle cover

The path-cover reduction uses only three bounded root graphs: a triangle, a
disjoint four-cycle/five-cycle pair, and three disjoint four-cycles.  A root
triangle needs no auxiliary edges.  This file gives small, explicit, fully
kernel-checked certificates for the other two root graphs.

The certificates were found by a finite exact-cover search.  The declarations
below do not trust that search: `decide` checks from the displayed triangle
lists that each side is a packing and that its covered graph has exactly the
claimed edge set.
-/

namespace Erdos207

open Finset

/-- The explicitly enumerable bad pairs in a proposed packing certificate. -/
def packingBadPairs {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Finset (TripleOn V × TripleOn V) :=
  (C.product C).filter fun TU ↦
    TU.1 ≠ TU.2 ∧ 1 < (TU.1.1 ∩ TU.2.1).card

/-- Executable certificate for pairwise linearity of a displayed finite
triple family. -/
def PackingCertificate {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Prop := packingBadPairs C = ∅

theorem isPackingOn_of_packingCertificate
    {V : Type*} [DecidableEq V] {C : TripleSystemOn V}
    (hC : PackingCertificate C) : IsPackingOn C := by
  intro u v huv T hTC huT hvT U hUC huU hvU
  by_contra hTU
  have hone : 1 < (T.1 ∩ U.1).card := Finset.one_lt_card.mpr
    ⟨u, Finset.mem_inter.mpr ⟨huT, huU⟩,
     v, Finset.mem_inter.mpr ⟨hvT, hvU⟩, huv⟩
  have hbad : (T, U) ∈ packingBadPairs C := by
    simp [packingBadPairs, hTC, hUC, hTU, hone]
  rw [hC] at hbad
  simp at hbad

/-- Covered graph edges are the union of the three graph edges contributed
by each displayed triple; no packing hypothesis is needed. -/
lemma coveredGraph_edgeFinset_eq_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : TripleSystemOn V) :
    (coveredGraph C).edgeFinset = C.biUnion tripleEdgeFinset := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        coveredGraph_adj, mem_biUnion, mk_mem_tripleEdgeFinset_iff]

/-- Edge-set form of `coveredGraph_edgeFinset_eq_biUnion`. -/
lemma coveredGraph_edgeSet_eq_biUnion
    {V : Type*} [DecidableEq V] (C : TripleSystemOn V) :
    (coveredGraph C).edgeSet =
      (C.biUnion tripleEdgeFinset : Set (Sym2 V)) := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
      simp only [SimpleGraph.mem_edgeSet, coveredGraph_adj, mem_coe,
        mem_biUnion, mk_mem_tripleEdgeFinset_iff]

lemma biUnion_union_eq {A X : Type*} [DecidableEq A] [DecidableEq X]
    (C D : Finset A) (f : A → Finset X) :
    (C ∪ D).biUnion f = C.biUnion f ∪ D.biUnion f := by
  ext x
  simp
  aesop

/-- Turning a loop-free finite edge list into a graph and back recovers the
same edge set. -/
lemma edgeSet_fromEdgeFinset {V : Type*} [DecidableEq V]
    (s : Finset (Sym2 V)) (hloop : ∀ e ∈ s, ¬ e.IsDiag) :
    (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet =
      (s : Set (Sym2 V)) := by
  ext e
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨fun h ↦ h.1, fun he ↦ ⟨he, hloop e he⟩⟩

/-- An exclusive graph absorber has an out-packing whose covered graph avoids
the root graph, and an in-packing which decomposes precisely the union of the
out graph and the root graph. -/
def IsExclusiveGraphAbsorberOn {V : Type*} [Fintype V] [DecidableEq V]
    (root : SimpleGraph V) (out inn : TripleSystemOn V) : Prop :=
  IsPackingOn out ∧ IsPackingOn inn ∧
    Disjoint (coveredGraph out) root ∧
    coveredGraph inn = coveredGraph out ⊔ root

lemma IsExclusiveGraphAbsorberOn.out_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    {root : SimpleGraph V} {out inn : TripleSystemOn V}
    (h : IsExclusiveGraphAbsorberOn root out inn) :
    IsTriangleDecomposition (coveredGraph out) out :=
  h.1.isTriangleDecomposition

lemma IsExclusiveGraphAbsorberOn.in_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    {root : SimpleGraph V} {out inn : TripleSystemOn V}
    (h : IsExclusiveGraphAbsorberOn root out inn) :
    IsTriangleDecomposition (coveredGraph out ⊔ root) inn := by
  rw [← h.2.2.2]
  exact h.2.1.isTriangleDecomposition

/-! ## The trivial absorber for a root triangle -/

@[simp]
lemma coveredGraph_empty {V : Type*} [DecidableEq V] :
    coveredGraph (∅ : TripleSystemOn V) = ⊥ := by
  ext u v
  simp [coveredGraph]

lemma isPackingOn_singleton {V : Type*} [DecidableEq V]
    (T : TripleOn V) : IsPackingOn ({T} : TripleSystemOn V) := by
  intro u v huv U hU huU hvU W hW huW hvW
  simpa using (Finset.mem_singleton.mp hU).trans
    (Finset.mem_singleton.mp hW).symm

/-- A single triangle is itself the in-side of an exclusive absorber; its
out-side is empty.  This is the third and trivial root type occurring in the
KSSS cycle cover. -/
theorem singleton_exclusiveGraphAbsorberOn
    {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    IsExclusiveGraphAbsorberOn (coveredGraph ({T} : TripleSystemOn V))
      ∅ {T} := by
  refine ⟨?_, isPackingOn_singleton T, ?_, ?_⟩
  · intro u v huv U hU
    simp at hU
  · simp
  · simp

/-! ## A four-cycle plus a five-cycle -/

def c4c5RootEdges : Finset (Sym2 (Fin 15)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3),
   s(4, 5), s(5, 6), s(6, 7), s(7, 8), s(4, 8)}

def c4c5RootGraph : SimpleGraph (Fin 15) :=
  SimpleGraph.fromEdgeSet (c4c5RootEdges : Set (Sym2 (Fin 15)))

def c4c5OutA : TripleSystem 15 :=
  {⟨{0, 10, 12}, by decide⟩,
   ⟨{0, 11, 13}, by decide⟩,
   ⟨{1, 12, 13}, by decide⟩,
   ⟨{2, 9, 10}, by decide⟩,
   ⟨{2, 11, 12}, by decide⟩}

def c4c5OutB : TripleSystem 15 :=
  {
   ⟨{3, 9, 11}, by decide⟩,
   ⟨{3, 10, 14}, by decide⟩,
   ⟨{4, 9, 13}, by decide⟩,
   ⟨{4, 12, 14}, by decide⟩,
   ⟨{5, 9, 12}, by decide⟩}

def c4c5OutC : TripleSystem 15 :=
  {
   ⟨{5, 10, 13}, by decide⟩,
   ⟨{6, 9, 14}, by decide⟩,
   ⟨{7, 11, 14}, by decide⟩,
   ⟨{8, 10, 11}, by decide⟩,
   ⟨{8, 13, 14}, by decide⟩}

def c4c5Out : TripleSystem 15 := c4c5OutA ∪ c4c5OutB ∪ c4c5OutC

def c4c5InA : TripleSystem 15 :=
  {⟨{0, 1, 13}, by decide⟩,
   ⟨{0, 3, 10}, by decide⟩,
   ⟨{0, 11, 12}, by decide⟩,
   ⟨{1, 2, 12}, by decide⟩,
   ⟨{2, 3, 9}, by decide⟩,
   ⟨{2, 10, 11}, by decide⟩}

def c4c5InB : TripleSystem 15 :=
  {
   ⟨{3, 11, 14}, by decide⟩,
   ⟨{4, 5, 13}, by decide⟩,
   ⟨{4, 8, 14}, by decide⟩,
   ⟨{4, 9, 12}, by decide⟩,
   ⟨{5, 6, 9}, by decide⟩,
   ⟨{5, 10, 12}, by decide⟩}

def c4c5InC : TripleSystem 15 :=
  {
   ⟨{6, 7, 14}, by decide⟩,
   ⟨{7, 8, 11}, by decide⟩,
   ⟨{8, 10, 13}, by decide⟩,
   ⟨{9, 10, 14}, by decide⟩,
   ⟨{9, 11, 13}, by decide⟩,
   ⟨{12, 13, 14}, by decide⟩}

def c4c5In : TripleSystem 15 := c4c5InA ∪ c4c5InB ∪ c4c5InC

theorem c4c5_isExclusiveGraphAbsorber :
    IsExclusiveGraphAbsorberOn c4c5RootGraph c4c5Out c4c5In := by
  have hroot : c4c5RootGraph.edgeSet =
      (c4c5RootEdges : Set (Sym2 (Fin 15))) := by
    apply edgeSet_fromEdgeFinset
    intro e he
    simp only [c4c5RootEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  refine ⟨isPackingOn_of_packingCertificate (by
      change packingBadPairs c4c5Out = ∅
      decide),
    isPackingOn_of_packingCertificate (by
      change packingBadPairs c4c5In = ∅
      decide), ?_, ?_⟩
  · apply SimpleGraph.disjoint_edgeSet.mp
    rw [coveredGraph_edgeSet_eq_biUnion, hroot]
    exact_mod_cast (by decide : Disjoint
      (c4c5Out.biUnion tripleEdgeFinset) c4c5RootEdges)
  · apply SimpleGraph.edgeSet_inj.mp
    rw [coveredGraph_edgeSet_eq_biUnion, SimpleGraph.edgeSet_sup,
      coveredGraph_edgeSet_eq_biUnion, hroot]
    ext e
    simp only [Set.mem_union, Finset.mem_coe]
    induction e using Sym2.ind with
    | h u v =>
        fin_cases u <;> fin_cases v <;> decide

/-! ## Three disjoint four-cycles -/

def threeC4RootEdges : Finset (Sym2 (Fin 18)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3),
   s(4, 5), s(5, 6), s(6, 7), s(4, 7),
   s(8, 9), s(9, 10), s(10, 11), s(8, 11)}

def threeC4RootGraph : SimpleGraph (Fin 18) :=
  SimpleGraph.fromEdgeSet (threeC4RootEdges : Set (Sym2 (Fin 18)))

def threeC4OutA : TripleSystem 18 :=
  {⟨{0, 12, 17}, by decide⟩,
   ⟨{1, 12, 15}, by decide⟩,
   ⟨{2, 14, 15}, by decide⟩,
   ⟨{3, 14, 17}, by decide⟩,
   ⟨{4, 15, 17}, by decide⟩}

def threeC4OutB : TripleSystem 18 :=
  {
   ⟨{5, 13, 17}, by decide⟩,
   ⟨{6, 13, 14}, by decide⟩,
   ⟨{6, 16, 17}, by decide⟩,
   ⟨{7, 15, 16}, by decide⟩,
   ⟨{8, 12, 16}, by decide⟩}

def threeC4OutC : TripleSystem 18 :=
  {
   ⟨{9, 12, 13}, by decide⟩,
   ⟨{9, 14, 16}, by decide⟩,
   ⟨{10, 12, 14}, by decide⟩,
   ⟨{10, 13, 15}, by decide⟩,
   ⟨{11, 13, 16}, by decide⟩}

def threeC4Out : TripleSystem 18 :=
  threeC4OutA ∪ threeC4OutB ∪ threeC4OutC

def threeC4InA : TripleSystem 18 :=
  {⟨{0, 1, 12}, by decide⟩,
   ⟨{0, 3, 17}, by decide⟩,
   ⟨{1, 2, 15}, by decide⟩,
   ⟨{2, 3, 14}, by decide⟩,
   ⟨{4, 5, 17}, by decide⟩}

def threeC4InB : TripleSystem 18 :=
  {
   ⟨{4, 7, 15}, by decide⟩,
   ⟨{5, 6, 13}, by decide⟩,
   ⟨{6, 7, 16}, by decide⟩,
   ⟨{6, 14, 17}, by decide⟩,
   ⟨{8, 9, 12}, by decide⟩}

def threeC4InC : TripleSystem 18 :=
  {
   ⟨{8, 11, 16}, by decide⟩,
   ⟨{9, 10, 14}, by decide⟩,
   ⟨{9, 13, 16}, by decide⟩,
   ⟨{10, 11, 13}, by decide⟩,
   ⟨{10, 12, 15}, by decide⟩}

def threeC4InD : TripleSystem 18 :=
  {
   ⟨{12, 13, 17}, by decide⟩,
   ⟨{12, 14, 16}, by decide⟩,
   ⟨{13, 14, 15}, by decide⟩,
   ⟨{15, 16, 17}, by decide⟩}

def threeC4In : TripleSystem 18 :=
  threeC4InA ∪ threeC4InB ∪ threeC4InC ∪ threeC4InD

def threeC4OutEdgesA : Finset (Sym2 (Fin 18)) :=
  {s(0, 12), s(0, 17), s(12, 17), s(1, 12), s(1, 15), s(12, 15),
   s(2, 14), s(2, 15), s(14, 15), s(3, 14), s(3, 17), s(14, 17),
   s(4, 15), s(4, 17), s(15, 17)}

def threeC4OutEdgesB : Finset (Sym2 (Fin 18)) :=
  {s(5, 13), s(5, 17), s(13, 17), s(6, 13), s(6, 14), s(13, 14),
   s(6, 16), s(6, 17), s(16, 17), s(7, 15), s(7, 16), s(15, 16),
   s(8, 12), s(8, 16), s(12, 16)}

def threeC4OutEdgesC : Finset (Sym2 (Fin 18)) :=
  {s(9, 12), s(9, 13), s(12, 13), s(9, 14), s(9, 16), s(14, 16),
   s(10, 12), s(10, 14), s(12, 14), s(10, 13), s(10, 15), s(13, 15),
   s(11, 13), s(11, 16), s(13, 16)}

def threeC4InEdgesA : Finset (Sym2 (Fin 18)) :=
  {s(0, 1), s(0, 12), s(1, 12), s(0, 3), s(0, 17), s(3, 17),
   s(1, 2), s(1, 15), s(2, 15), s(2, 3), s(2, 14), s(3, 14),
   s(4, 5), s(4, 17), s(5, 17)}

def threeC4InEdgesB : Finset (Sym2 (Fin 18)) :=
  {s(4, 7), s(4, 15), s(7, 15), s(5, 6), s(5, 13), s(6, 13),
   s(6, 7), s(6, 16), s(7, 16), s(6, 14), s(6, 17), s(14, 17),
   s(8, 9), s(8, 12), s(9, 12)}

def threeC4InEdgesC : Finset (Sym2 (Fin 18)) :=
  {s(8, 11), s(8, 16), s(11, 16), s(9, 10), s(9, 14), s(10, 14),
   s(9, 13), s(9, 16), s(13, 16), s(10, 11), s(10, 13), s(11, 13),
   s(10, 12), s(10, 15), s(12, 15)}

def threeC4InEdgesD : Finset (Sym2 (Fin 18)) :=
  {s(12, 13), s(12, 17), s(13, 17), s(12, 14), s(12, 16), s(14, 16),
   s(13, 14), s(13, 15), s(14, 15), s(15, 16), s(15, 17), s(16, 17)}

def threeC4OutEdges : Finset (Sym2 (Fin 18)) :=
  threeC4OutEdgesA ∪ threeC4OutEdgesB ∪ threeC4OutEdgesC

def threeC4InEdges : Finset (Sym2 (Fin 18)) :=
  threeC4InEdgesA ∪ threeC4InEdgesB ∪ threeC4InEdgesC ∪ threeC4InEdgesD

lemma threeC4OutA_edges :
    threeC4OutA.biUnion tripleEdgeFinset = threeC4OutEdgesA := by decide

lemma threeC4OutB_edges :
    threeC4OutB.biUnion tripleEdgeFinset = threeC4OutEdgesB := by decide

lemma threeC4OutC_edges :
    threeC4OutC.biUnion tripleEdgeFinset = threeC4OutEdgesC := by decide

lemma threeC4InA_edges :
    threeC4InA.biUnion tripleEdgeFinset = threeC4InEdgesA := by decide

lemma threeC4InB_edges :
    threeC4InB.biUnion tripleEdgeFinset = threeC4InEdgesB := by decide

lemma threeC4InC_edges :
    threeC4InC.biUnion tripleEdgeFinset = threeC4InEdgesC := by decide

lemma threeC4InD_edges :
    threeC4InD.biUnion tripleEdgeFinset = threeC4InEdgesD := by decide

lemma threeC4Out_edges :
    threeC4Out.biUnion tripleEdgeFinset = threeC4OutEdges := by
  rw [threeC4Out, biUnion_union_eq, biUnion_union_eq,
    threeC4OutA_edges, threeC4OutB_edges, threeC4OutC_edges]
  rfl

lemma threeC4In_edges :
    threeC4In.biUnion tripleEdgeFinset = threeC4InEdges := by
  rw [threeC4In, biUnion_union_eq, biUnion_union_eq, biUnion_union_eq,
    threeC4InA_edges, threeC4InB_edges, threeC4InC_edges, threeC4InD_edges]
  rfl

def ThreeC4EdgeEqualityAt (u v : Fin 18) : Prop :=
  (((s(u, v) ∈ threeC4InEdgesA ∨
      s(u, v) ∈ threeC4InEdgesB) ∨
      s(u, v) ∈ threeC4InEdgesC) ∨
      s(u, v) ∈ threeC4InEdgesD) ↔
  (((s(u, v) ∈ threeC4OutEdgesA ∨
      s(u, v) ∈ threeC4OutEdgesB) ∨
      s(u, v) ∈ threeC4OutEdgesC) ∨
      s(u, v) ∈ threeC4RootEdges)

lemma threeC4_edge_row_0 (v : Fin 18) : ThreeC4EdgeEqualityAt 0 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_1 (v : Fin 18) : ThreeC4EdgeEqualityAt 1 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_2 (v : Fin 18) : ThreeC4EdgeEqualityAt 2 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_3 (v : Fin 18) : ThreeC4EdgeEqualityAt 3 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_4 (v : Fin 18) : ThreeC4EdgeEqualityAt 4 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_5 (v : Fin 18) : ThreeC4EdgeEqualityAt 5 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_6 (v : Fin 18) : ThreeC4EdgeEqualityAt 6 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_7 (v : Fin 18) : ThreeC4EdgeEqualityAt 7 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_8 (v : Fin 18) : ThreeC4EdgeEqualityAt 8 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_9 (v : Fin 18) : ThreeC4EdgeEqualityAt 9 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_10 (v : Fin 18) : ThreeC4EdgeEqualityAt 10 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_11 (v : Fin 18) : ThreeC4EdgeEqualityAt 11 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_12 (v : Fin 18) : ThreeC4EdgeEqualityAt 12 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_13 (v : Fin 18) : ThreeC4EdgeEqualityAt 13 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_14 (v : Fin 18) : ThreeC4EdgeEqualityAt 14 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_15 (v : Fin 18) : ThreeC4EdgeEqualityAt 15 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_16 (v : Fin 18) : ThreeC4EdgeEqualityAt 16 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

lemma threeC4_edge_row_17 (v : Fin 18) : ThreeC4EdgeEqualityAt 17 v := by
  unfold ThreeC4EdgeEqualityAt
  fin_cases v <;> decide

theorem threeC4_isExclusiveGraphAbsorber :
    IsExclusiveGraphAbsorberOn threeC4RootGraph threeC4Out threeC4In := by
  have hroot : threeC4RootGraph.edgeSet =
      (threeC4RootEdges : Set (Sym2 (Fin 18))) := by
    apply edgeSet_fromEdgeFinset
    intro e he
    simp only [threeC4RootEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide
  refine ⟨isPackingOn_of_packingCertificate (by
      change packingBadPairs threeC4Out = ∅
      decide),
    isPackingOn_of_packingCertificate (by
      change packingBadPairs threeC4In = ∅
      decide), ?_, ?_⟩
  · apply SimpleGraph.disjoint_edgeSet.mp
    rw [coveredGraph_edgeSet_eq_biUnion, hroot]
    exact_mod_cast (by decide : Disjoint
      (threeC4Out.biUnion tripleEdgeFinset) threeC4RootEdges)
  · apply SimpleGraph.edgeSet_inj.mp
    rw [coveredGraph_edgeSet_eq_biUnion, SimpleGraph.edgeSet_sup,
      coveredGraph_edgeSet_eq_biUnion, hroot]
    rw [threeC4In_edges, threeC4Out_edges]
    ext e
    simp only [Set.mem_union, Finset.mem_coe]
    induction e using Sym2.ind with
    | h u v =>
        simp only [threeC4InEdges, threeC4OutEdges, mem_union]
        change ThreeC4EdgeEqualityAt u v
        fin_cases u
        · exact threeC4_edge_row_0 v
        · exact threeC4_edge_row_1 v
        · exact threeC4_edge_row_2 v
        · exact threeC4_edge_row_3 v
        · exact threeC4_edge_row_4 v
        · exact threeC4_edge_row_5 v
        · exact threeC4_edge_row_6 v
        · exact threeC4_edge_row_7 v
        · exact threeC4_edge_row_8 v
        · exact threeC4_edge_row_9 v
        · exact threeC4_edge_row_10 v
        · exact threeC4_edge_row_11 v
        · exact threeC4_edge_row_12 v
        · exact threeC4_edge_row_13 v
        · exact threeC4_edge_row_14 v
        · exact threeC4_edge_row_15 v
        · exact threeC4_edge_row_16 v
        · exact threeC4_edge_row_17 v

end Erdos207
