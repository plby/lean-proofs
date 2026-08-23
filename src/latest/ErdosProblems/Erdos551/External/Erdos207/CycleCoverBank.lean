/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.AbsorberBank
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A bounded bank for the vertex-disjoint cycle templates

For a finite root set `Y`, this file attaches the three vertex-disjoint
template absorbers along every injection of their root vertices into `Y`.
The six non-root vertices of every nontrivial copy are tagged by that copy.

KSSS Definition 4.4 also permits the four- and five-cycles in a root group
to share vertices.  Thus this module is a checked finite subcase and an
attachment/gluing test; the full cycle cover additionally uses the generic
exclusive absorber for every bounded triangle-divisible root graph.
-/

namespace Erdos207

open Finset

noncomputable section

inductive CycleCoverCopy (Y : Type*) where
  | triangle (f : Fin 3 ↪ Y)
  | c4c5 (f : Fin 9 ↪ Y)
  | threeC4 (f : Fin 12 ↪ Y)
  deriving DecidableEq, Fintype

/-- Original root vertices, followed by six private vertices for every bank
copy.  Triangle copies do not use their allocated private vertices. -/
abbrev CycleCoverVertex (Y : Type*) :=
  Y ⊕ (CycleCoverCopy Y × Fin 6)

def cycleCoverBaseEmbedding (Y : Type*) : Y ↪ CycleCoverVertex Y :=
  Function.Embedding.inl

def c4c5AttachmentEmbedding {Y : Type*} (f : Fin 9 ↪ Y) :
    Fin 15 ↪ CycleCoverVertex Y :=
  finSumFinEquiv.symm.toEmbedding |>.trans <|
    Function.Embedding.sumMap
      f (Function.Embedding.sectR (CycleCoverCopy.c4c5 f) (Fin 6))

def threeC4AttachmentEmbedding {Y : Type*} (f : Fin 12 ↪ Y) :
    Fin 18 ↪ CycleCoverVertex Y :=
  finSumFinEquiv.symm.toEmbedding |>.trans <|
    Function.Embedding.sumMap
      f (Function.Embedding.sectR (CycleCoverCopy.threeC4 f) (Fin 6))

def finThreeTriple : TripleOn (Fin 3) :=
  ⟨univ, by simp⟩

def cycleCoverTriangleTriple {Y : Type*} [DecidableEq Y]
    (f : Fin 3 ↪ Y) : TripleOn (CycleCoverVertex Y) :=
  mapTriple (f.trans (cycleCoverBaseEmbedding Y)) finThreeTriple

def cycleCoverRoot {Y : Type*} [DecidableEq Y]
    (i : CycleCoverCopy Y) : SimpleGraph (CycleCoverVertex Y) :=
  match i with
  | .triangle f => coveredGraph {cycleCoverTriangleTriple f}
  | .c4c5 f => c4c5RootGraph.map (c4c5AttachmentEmbedding f)
  | .threeC4 f => threeC4RootGraph.map (threeC4AttachmentEmbedding f)

def cycleCoverOut {Y : Type*} [DecidableEq Y]
    (i : CycleCoverCopy Y) : TripleSystemOn (CycleCoverVertex Y) :=
  match i with
  | .triangle _ => ∅
  | .c4c5 f => mapTripleSystem (c4c5AttachmentEmbedding f) c4c5Out
  | .threeC4 f => mapTripleSystem (threeC4AttachmentEmbedding f) threeC4Out

def cycleCoverIn {Y : Type*} [DecidableEq Y]
    (i : CycleCoverCopy Y) : TripleSystemOn (CycleCoverVertex Y) :=
  match i with
  | .triangle f => {cycleCoverTriangleTriple f}
  | .c4c5 f => mapTripleSystem (c4c5AttachmentEmbedding f) c4c5In
  | .threeC4 f => mapTripleSystem (threeC4AttachmentEmbedding f) threeC4In

/-- Every member of the universal bank is an exact exclusive absorber. -/
theorem cycleCoverCopy_isExclusiveGraphAbsorber
    {Y : Type*} [Fintype Y] [DecidableEq Y] (i : CycleCoverCopy Y) :
    IsExclusiveGraphAbsorberOn (cycleCoverRoot i)
      (cycleCoverOut i) (cycleCoverIn i) := by
  cases i with
  | triangle f =>
      exact singleton_exclusiveGraphAbsorberOn (cycleCoverTriangleTriple f)
  | c4c5 f =>
      exact c4c5_isExclusiveGraphAbsorber.map (c4c5AttachmentEmbedding f)
  | threeC4 f =>
      exact threeC4_isExclusiveGraphAbsorber.map (threeC4AttachmentEmbedding f)

/-- A vertex is either a root vertex, or a private vertex tagged by `i`. -/
def BelongsToCycleCoverCopy {Y : Type*} (i : CycleCoverCopy Y) :
    CycleCoverVertex Y → Prop
  | Sum.inl _ => True
  | Sum.inr (j, _) => j = i

/-- A private vertex tagged by `i`. -/
def IsPrivateForCycleCoverCopy {Y : Type*} (i : CycleCoverCopy Y) :
    CycleCoverVertex Y → Prop
  | Sum.inl _ => False
  | Sum.inr (j, _) => j = i

lemma privateFor_implies_belongs {Y : Type*} {i : CycleCoverCopy Y}
    {v : CycleCoverVertex Y} (h : IsPrivateForCycleCoverCopy i v) :
    BelongsToCycleCoverCopy i v := by
  cases v with
  | inl y => exact h.elim
  | inr p => exact h

lemma privateFor_and_belongs_iff_eq {Y : Type*}
    {i j : CycleCoverCopy Y} {v : CycleCoverVertex Y}
    (hi : IsPrivateForCycleCoverCopy i v)
    (hj : BelongsToCycleCoverCopy j v) : i = j := by
  cases v with
  | inl y => exact hi.elim
  | inr p => exact hi.symm.trans hj

/-- Executable source-certificate: every out-edge of the `C4 ∪ C5`
absorber has a non-root endpoint. -/
lemma c4c5Out_edge_has_private_source :
    ∀ u v : Fin 15, (coveredGraph c4c5Out).Adj u v →
      (∃ k : Fin 6, (finSumFinEquiv (m := 9) (n := 6)).symm u = Sum.inr k) ∨
        ∃ k : Fin 6, (finSumFinEquiv (m := 9) (n := 6)).symm v = Sum.inr k := by
  decide

/-- Executable source-certificate: every out-edge of the `3C4` absorber has
a non-root endpoint. -/
lemma threeC4Out_edge_has_private_source :
    ∀ u v : Fin 18, (coveredGraph threeC4Out).Adj u v →
      (∃ k : Fin 6, (finSumFinEquiv (m := 12) (n := 6)).symm u = Sum.inr k) ∨
        ∃ k : Fin 6, (finSumFinEquiv (m := 12) (n := 6)).symm v = Sum.inr k := by
  decide

/-- Executable source-certificate: all root edges of the `C4 ∪ C5` graph
have both endpoints among the first nine vertices. -/
lemma c4c5Root_edge_has_root_source :
    ∀ u v : Fin 15, c4c5RootGraph.Adj u v →
      (∃ a : Fin 9, (finSumFinEquiv (m := 9) (n := 6)).symm u = Sum.inl a) ∧
        ∃ b : Fin 9, (finSumFinEquiv (m := 9) (n := 6)).symm v = Sum.inl b := by
  have hroot : c4c5RootGraph.edgeSet =
      (c4c5RootEdges : Set (Sym2 (Fin 15))) := by
    apply edgeSet_fromEdgeFinset
    intro e he
    simp only [c4c5RootEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  intro u v huv
  change s(u, v) ∈ c4c5RootGraph.edgeSet at huv
  rw [hroot] at huv
  change s(u, v) ∈ c4c5RootEdges at huv
  simp only [c4c5RootEdges, mem_insert, mem_singleton] at huv
  rcases huv with h | h | h | h | h | h | h | h | h <;>
    rw [Sym2.eq_iff] at h <;>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Executable source-certificate: all root edges of the `3C4` graph have
both endpoints among the first twelve vertices. -/
lemma threeC4Root_edge_has_root_source :
    ∀ u v : Fin 18, threeC4RootGraph.Adj u v →
      (∃ a : Fin 12, (finSumFinEquiv (m := 12) (n := 6)).symm u = Sum.inl a) ∧
        ∃ b : Fin 12, (finSumFinEquiv (m := 12) (n := 6)).symm v = Sum.inl b := by
  have hroot : threeC4RootGraph.edgeSet =
      (threeC4RootEdges : Set (Sym2 (Fin 18))) := by
    apply edgeSet_fromEdgeFinset
    intro e he
    simp only [threeC4RootEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide
  intro u v huv
  change s(u, v) ∈ threeC4RootGraph.edgeSet at huv
  rw [hroot] at huv
  change s(u, v) ∈ threeC4RootEdges at huv
  simp only [threeC4RootEdges, mem_insert, mem_singleton] at huv
  rcases huv with h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [Sym2.eq_iff] at h <;>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

lemma c4c5AttachmentEmbedding_belongs {Y : Type*}
    (f : Fin 9 ↪ Y) (u : Fin 15) :
    BelongsToCycleCoverCopy (.c4c5 f) (c4c5AttachmentEmbedding f u) := by
  rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply u]
  cases (finSumFinEquiv (m := 9) (n := 6)).symm u <;>
    simp [c4c5AttachmentEmbedding, BelongsToCycleCoverCopy]

lemma threeC4AttachmentEmbedding_belongs {Y : Type*}
    (f : Fin 12 ↪ Y) (u : Fin 18) :
    BelongsToCycleCoverCopy (.threeC4 f) (threeC4AttachmentEmbedding f u) := by
  rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply u]
  cases (finSumFinEquiv (m := 12) (n := 6)).symm u <;>
    simp [threeC4AttachmentEmbedding, BelongsToCycleCoverCopy]

lemma c4c5AttachmentEmbedding_private {Y : Type*}
    (f : Fin 9 ↪ Y) (u : Fin 15) (k : Fin 6)
    (hu : (finSumFinEquiv (m := 9) (n := 6)).symm u = Sum.inr k) :
    IsPrivateForCycleCoverCopy (.c4c5 f) (c4c5AttachmentEmbedding f u) := by
  rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply u, hu]
  simp [c4c5AttachmentEmbedding, IsPrivateForCycleCoverCopy]

lemma threeC4AttachmentEmbedding_private {Y : Type*}
    (f : Fin 12 ↪ Y) (u : Fin 18) (k : Fin 6)
    (hu : (finSumFinEquiv (m := 12) (n := 6)).symm u = Sum.inr k) :
    IsPrivateForCycleCoverCopy (.threeC4 f)
      (threeC4AttachmentEmbedding f u) := by
  rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply u, hu]
  simp [threeC4AttachmentEmbedding, IsPrivateForCycleCoverCopy]

/-- Every edge of an out-graph remains inside one copy and has at least one
private endpoint. -/
lemma cycleCoverOut_edge_structure {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : CycleCoverCopy Y) {u v : CycleCoverVertex Y}
    (huv : (coveredGraph (cycleCoverOut i)).Adj u v) :
    BelongsToCycleCoverCopy i u ∧ BelongsToCycleCoverCopy i v ∧
      (IsPrivateForCycleCoverCopy i u ∨ IsPrivateForCycleCoverCopy i v) := by
  cases i with
  | triangle f =>
      simp [cycleCoverOut, coveredGraph] at huv
  | c4c5 f =>
      simp only [cycleCoverOut, coveredGraph_mapTripleSystem,
        SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      refine ⟨c4c5AttachmentEmbedding_belongs f a,
        c4c5AttachmentEmbedding_belongs f b, ?_⟩
      rcases c4c5Out_edge_has_private_source a b hab with
        ⟨k, hk⟩ | ⟨k, hk⟩
      · exact Or.inl (c4c5AttachmentEmbedding_private f a k hk)
      · exact Or.inr (c4c5AttachmentEmbedding_private f b k hk)
  | threeC4 f =>
      simp only [cycleCoverOut, coveredGraph_mapTripleSystem,
        SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      refine ⟨threeC4AttachmentEmbedding_belongs f a,
        threeC4AttachmentEmbedding_belongs f b, ?_⟩
      rcases threeC4Out_edge_has_private_source a b hab with
        ⟨k, hk⟩ | ⟨k, hk⟩
      · exact Or.inl (threeC4AttachmentEmbedding_private f a k hk)
      · exact Or.inr (threeC4AttachmentEmbedding_private f b k hk)

lemma c4c5AttachmentEmbedding_root {Y : Type*}
    (f : Fin 9 ↪ Y) (u : Fin 15) (a : Fin 9)
    (hu : (finSumFinEquiv (m := 9) (n := 6)).symm u = Sum.inl a) :
    c4c5AttachmentEmbedding f u = Sum.inl (f a) := by
  rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply u, hu]
  simp [c4c5AttachmentEmbedding]

lemma threeC4AttachmentEmbedding_root {Y : Type*}
    (f : Fin 12 ↪ Y) (u : Fin 18) (a : Fin 12)
    (hu : (finSumFinEquiv (m := 12) (n := 6)).symm u = Sum.inl a) :
    threeC4AttachmentEmbedding f u = Sum.inl (f a) := by
  rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply u, hu]
  simp [threeC4AttachmentEmbedding]

/-- Both endpoints of every bank root edge are original vertices in `Y`. -/
lemma cycleCoverRoot_edge_base {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : CycleCoverCopy Y) {u v : CycleCoverVertex Y}
    (huv : (cycleCoverRoot i).Adj u v) :
    (∃ y : Y, u = Sum.inl y) ∧ ∃ z : Y, v = Sum.inl z := by
  cases i with
  | triangle f =>
      obtain ⟨T, hT, huT, hvT, huvne⟩ := huv
      simp only [cycleCoverRoot, mem_singleton] at hT
      subst T
      obtain ⟨a, ha, hau⟩ := Finset.mem_map.mp huT
      obtain ⟨b, hb, hbv⟩ := Finset.mem_map.mp hvT
      exact ⟨⟨f a, hau.symm⟩, ⟨f b, hbv.symm⟩⟩
  | c4c5 f =>
      simp only [cycleCoverRoot, SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ :=
        c4c5Root_edge_has_root_source a b hab
      exact ⟨⟨f x, c4c5AttachmentEmbedding_root f a x hx⟩,
        ⟨f y, c4c5AttachmentEmbedding_root f b y hy⟩⟩
  | threeC4 f =>
      simp only [cycleCoverRoot, SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ :=
        threeC4Root_edge_has_root_source a b hab
      exact ⟨⟨f x, threeC4AttachmentEmbedding_root f a x hx⟩,
        ⟨f y, threeC4AttachmentEmbedding_root f b y hy⟩⟩

/-- Distinct out-gadgets are edge-disjoint because each out-edge has a
private endpoint tagged by its copy. -/
lemma cycleCoverOut_pairwise_disjoint {Y : Type*} [Fintype Y] [DecidableEq Y]
    {i j : CycleCoverCopy Y} (hij : i ≠ j) :
    Disjoint (coveredGraph (cycleCoverOut i))
      (coveredGraph (cycleCoverOut j)) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e hei hej
  induction e using Sym2.ind with
  | h u v =>
      have hi := cycleCoverOut_edge_structure i hei
      have hj := cycleCoverOut_edge_structure j hej
      rcases hi.2.2 with hpriv | hpriv
      · exact hij (privateFor_and_belongs_iff_eq hpriv hj.1)
      · exact hij (privateFor_and_belongs_iff_eq hpriv hj.2.1)

/-- Every out-gadget is edge-disjoint from every potential root graph. -/
lemma cycleCoverOut_root_disjoint {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i j : CycleCoverCopy Y) :
    Disjoint (coveredGraph (cycleCoverOut i)) (cycleCoverRoot j) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e hei hej
  induction e using Sym2.ind with
  | h u v =>
      have hi := cycleCoverOut_edge_structure i hei
      obtain ⟨⟨y, huy⟩, ⟨z, hvz⟩⟩ := cycleCoverRoot_edge_base j hej
      change u = Sum.inl y at huy
      change v = Sum.inl z at hvz
      rcases hi.2.2 with hpriv | hpriv
      · simpa [huy, IsPrivateForCycleCoverCopy] using hpriv
      · simpa [hvz, IsPrivateForCycleCoverCopy] using hpriv

/-- The vertex-disjoint-template bank absorbs every edge-disjoint selected
family of its root graphs. -/
theorem universalCycleCoverBank_switch
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (selected : Finset (CycleCoverCopy Y))
    (hroots : ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
      Disjoint (cycleCoverRoot i) (cycleCoverRoot j)) :
    IsTriangleDecomposition
      (graphSup univ
        (switchedAbsorberGraph selected cycleCoverRoot cycleCoverOut))
      (tripleUnion univ
        (switchedAbsorberTriples selected cycleCoverOut cycleCoverIn)) := by
  apply exclusiveAbsorberBank_switch_of_switched_disjoint
  · intro i hi
    exact cycleCoverCopy_isExclusiveGraphAbsorber i
  · intro i hi j hj hij
    by_cases hisel : i ∈ selected <;> by_cases hjsel : j ∈ selected
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_true]
      rw [disjoint_sup_left, disjoint_sup_right, disjoint_sup_right]
      exact ⟨⟨cycleCoverOut_pairwise_disjoint hij,
        cycleCoverOut_root_disjoint i j⟩,
        ⟨(cycleCoverOut_root_disjoint j i).symm,
          hroots i hisel j hjsel hij⟩⟩
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_true, if_false,
        sup_bot_eq]
      rw [disjoint_sup_left]
      exact ⟨cycleCoverOut_pairwise_disjoint hij,
        (cycleCoverOut_root_disjoint j i).symm⟩
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_true, if_false,
        sup_bot_eq]
      rw [disjoint_sup_right]
      exact ⟨cycleCoverOut_pairwise_disjoint hij,
        cycleCoverOut_root_disjoint i j⟩
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_false, sup_bot_eq]
      exact cycleCoverOut_pairwise_disjoint hij

end

end Erdos207
