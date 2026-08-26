import ErdosProblems.Erdos547.LeafExtension
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The subtree obtained by deleting the leaves

For a tree of order at least three, its vertices of degree at least two induce
a nonempty tree. Every omitted vertex has its unique neighbour in that tree.
The core has at most twice the size of either bipartition class, minus one.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph BigOperators

variable {U : Type*} [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj]

/-- The vertices which are not leaves in a nontrivial tree. -/
def treeCore : Set U := {v | 2 ≤ T.degree v}

/-- A leaf of a connected graph with at least three vertices has a nonleaf
as its unique neighbour. -/
theorem leaf_neighbor_mem_treeCore (hT : T.Connected) (hcard : 3 ≤ Fintype.card U)
    {v p : U} (hv : T.degree v = 1) (hvp : T.Adj v p) : p ∈ treeCore T := by
  classical
  let A := ({v}ᶜ : Set U)
  let p' : A := ⟨p, by simpa [A] using hvp.ne'⟩
  have hA : Fintype.card A = Fintype.card U - 1 := by
    change Fintype.card ↑({v}ᶜ : Set U) = Fintype.card U - 1
    rw [Fintype.card_compl_set]
    simp
  have hAn : 1 < Fintype.card A := by omega
  let : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp hAn
  have hconn : (T.induce A).Connected :=
    hT.induce_compl_singleton_of_degree_eq_one hv
  have hpos := hconn.preconnected.degree_pos_of_nontrivial p'
  obtain ⟨q, hpq⟩ := ((T.induce A).degree_pos_iff_exists_adj p').mp hpos
  have hp : 0 < T.degree p := hvp.degree_pos_right
  have hpne : T.degree p ≠ 1 := by
    intro h
    obtain ⟨r, _, hr⟩ := T.degree_eq_one_iff_existsUnique_adj.mp h
    have hq : q.val = v := (hr q.val hpq).trans (hr v hvp.symm).symm
    exact q.property (by simp [A, hq])
  change 2 ≤ T.degree p
  omega

/-- The core is nonempty once the exceptional trees of order one and two are
excluded. -/
theorem treeCore_nonempty (hT : T.IsTree) (hcard : 3 ≤ Fintype.card U) :
    (treeCore T).Nonempty := by
  classical
  let : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨p, hvp, _⟩ := T.degree_eq_one_iff_existsUnique_adj.mp hv
  exact ⟨p, leaf_neighbor_mem_treeCore T hT.connected hcard hv hvp⟩

/-- Removing all leaves of a tree of order at least three leaves a tree. -/
theorem isTree_treeCore (hT : T.IsTree) (hcard : 3 ≤ Fintype.card U) :
    (T.induce (treeCore T)).IsTree := by
  classical
  have hpre : (T.induce (treeCore T)).Preconnected := by
    apply hT.connected.preconnected.induce_of_degree_eq_one
    intro v hv
    have hd : (T.neighborFinset v).card ≤ 1 := by
      rw [T.card_neighborFinset_eq_degree]
      change ¬ 2 ≤ T.degree v at hv
      omega
    intro x hx y hy
    exact (Finset.card_le_one.mp hd) x (by simpa using hx) y (by simpa using hy)
  let : Nonempty (treeCore T) := (treeCore_nonempty T hT hcard).to_subtype
  exact ⟨⟨hpre⟩, hT.isAcyclic.induce _⟩

/-- Every deleted leaf has exactly one neighbour, and this neighbour is in the
core. This form supplies the parent data needed by Hall leaf restoration. -/
theorem exists_treeCore_parent (hT : T.IsTree) (hcard : 3 ≤ Fintype.card U) :
    ∃ parent : ((treeCore T)ᶜ : Set U) → treeCore T,
      ∀ x : ((treeCore T)ᶜ : Set U), ∀ y, T.Adj x.val y → y = (parent x).val := by
  classical
  let : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hparent (x : ((treeCore T)ᶜ : Set U)) :
      ∃ p : treeCore T, ∀ y, T.Adj x.val y → y = p.val := by
    have hnot : ¬ 2 ≤ T.degree x.val := x.property
    have hpos := hT.connected.preconnected.degree_pos_of_nontrivial x.val
    have hx : T.degree x.val = 1 := by omega
    obtain ⟨p, hxp, hp⟩ := T.degree_eq_one_iff_existsUnique_adj.mp hx
    exact ⟨⟨p, leaf_neighbor_mem_treeCore T hT.connected hcard hx hxp⟩, hp⟩
  exact ⟨fun x ↦ (hparent x).choose, fun x ↦ (hparent x).choose_spec⟩

open scoped Classical in
/-- In either bipartition class, the number of nonleaves is at most the size
of the opposite class minus one. -/
theorem card_nonleaves_part_add_one_le (hT : T.IsTree) [Nontrivial U]
    (s t : Finset U) (hpart : T.IsBipartiteWith (s : Set U) (t : Set U))
    (hcover : s ∪ t = Finset.univ) :
    (t.filter fun v ↦ 2 ≤ T.degree v).card + 1 ≤ s.card := by
  classical
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hpart
  have hbound : t.card + (t.filter fun v ↦ 2 ≤ T.degree v).card ≤
      ∑ v ∈ t, T.degree v := by
    calc
      _ = ∑ v ∈ t, (1 + if 2 ≤ T.degree v then 1 else 0) := by
        simp [Finset.sum_add_distrib]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        have hpos := hT.connected.preconnected.degree_pos_of_nontrivial v
        split_ifs <;> omega
  have hdis : Disjoint s t := Finset.disjoint_coe.mp hpart.disjoint
  have hcard : s.card + t.card = Fintype.card U := by
    rw [← Finset.card_union_of_disjoint hdis, hcover, Finset.card_univ]
  rw [hsum] at hbound
  have hedges := hT.card_edgeFinset
  omega

open scoped Classical in
/-- A tree core has at most `2 * |s| - 1` vertices for either bipartition class
`s`. The additive form avoids truncated subtraction at small cardinalities. -/
theorem card_treeCore_add_one_le (hT : T.IsTree) [Nontrivial U]
    (s t : Finset U) (hpart : T.IsBipartiteWith (s : Set U) (t : Set U))
    (hcover : s ∪ t = Finset.univ) :
    Fintype.card (treeCore T) + 1 ≤ 2 * s.card := by
  classical
  have hsmall := card_nonleaves_part_add_one_le T hT s t hpart hcover
  have hsplit : Fintype.card (treeCore T) =
      (s.filter fun v ↦ 2 ≤ T.degree v).card +
        (t.filter fun v ↦ 2 ≤ T.degree v).card := by
    rw [← Finset.card_union_of_disjoint
      ((Finset.disjoint_coe.mp hpart.disjoint).mono (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))]
    rw [← Finset.filter_union, hcover]
    apply Fintype.card_of_subtype
    intro v
    simp [treeCore]
  have hs := Finset.card_filter_le s (fun v ↦ 2 ≤ T.degree v)
  omega

end Erdos547

#print axioms Erdos547.isTree_treeCore
#print axioms Erdos547.exists_treeCore_parent
#print axioms Erdos547.card_treeCore_add_one_le
