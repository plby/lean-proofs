import ErdosProblems.Erdos577.FullLeafSparseUnique

/-! The heavy family and the actual sparse and matching vertex sets for the ten-row count. -/

namespace Erdos577.FullLeafEquality

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def attachedVertices (p : Paw G) (s a : Finset V) (y : V) (j : Finset V) :
    Finset V := by
  classical
  exact ((s.erase y) ∪ insert (p.vertices 3) a).filter
    (fun v ↦ FullLeafSparse.Attached G p s a y v j)

def matchedFirst (p : Paw G) (s a : Finset V) (y : V) : Finset V :=
  (s.erase y).filter (fun v ↦ 0 < degreeIn G v (insert (p.vertices 3) a))

def matchedSecond (p : Paw G) (s a : Finset V) (y : V) : Finset V :=
  (insert (p.vertices 3) a).filter (fun v ↦ 0 < degreeIn G v (s.erase y))

lemma mem_attachedVertices {p : Paw G} {s a j : Finset V} {y v : V} :
    v ∈ attachedVertices p s a y j ↔ FullLeafSparse.Attached G p s a y v j := by
  classical
  constructor
  · exact fun hv ↦ (mem_filter.mp hv).2
  · intro hv
    apply mem_filter.mpr
    refine ⟨?_, hv⟩
    exact hv.1.elim (fun hh ↦ mem_union_left _ hh.1) (fun hh ↦ mem_union_right _ hh.1)

lemma attachedVertices_subset (p : Paw G) (s a : Finset V) (y : V) (j : Finset V) :
    attachedVertices p s a y j ⊆ (s.erase y) ∪ insert (p.vertices 3) a := by
  classical
  exact filter_subset _ _

variable [Fintype V]

def further (c : TriangleChain G) (s a : Finset V) : Finset (Finset V) := c.blocks \ {s, a}

def heavy (c : TriangleChain G) (p : Paw G) (s a : Finset V) : Finset (Finset V) :=
  (further c s a).filter
    (fun j ↦ 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)

noncomputable def covered (c : TriangleChain G) (p : Paw G) (s a : Finset V) (y : V) :
    Finset V := (heavy c p s a).biUnion (attachedVertices p s a y)

omit [DecidableRel G.Adj] in
lemma mem_further {c : TriangleChain G} {s a j : Finset V} :
    j ∈ further c s a ↔ j ∈ c.blocks ∧ j ≠ s ∧ j ≠ a := by
  simp only [further, mem_sdiff, mem_insert, mem_singleton, not_or]

lemma mem_heavy {c : TriangleChain G} {p : Paw G} {s a j : Finset V} :
    j ∈ heavy c p s a ↔ (j ∈ c.blocks ∧ j ≠ s ∧ j ≠ a) ∧
      21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j := by
  simp only [heavy, mem_filter, mem_further]

lemma mem_covered {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y v : V} :
    v ∈ covered c p s a y ↔ ∃ j ∈ heavy c p s a, FullLeafSparse.Attached G p s a y v j := by
  simp only [covered, mem_biUnion, mem_attachedVertices]

end Erdos577.FullLeafEquality

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.three_le_parameter {k : ℕ} (hcard : Fintype.card V = 4 * k) : 3 ≤ k := by
  have hb := card_le_card (subset_univ (p.support ∪ s ∪ a))
  rw [h.total_card, card_univ, hcard] at hb
  omega

lemma Configuration.further_card {k : ℕ} (hcard : Fintype.card V = 4 * k) :
    (FullLeafEquality.further c s a).card = k - 3 := by
  have hsub : ({s, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr h.core)
  have hvertices := c.card_vertices
  rw [FullLeafEquality.further, card_sdiff_of_subset hsub, card_pair h.different.symm]
  omega

lemma Configuration.triple_second_disjoint : Disjoint (s.erase y) (insert (p.vertices 3) a) :=
  h.five_disjoint_core.mono (fun _ hv ↦ mem_insert_of_mem (mem_erase.mp hv).2) h.second_five_subset

lemma Configuration.sparse_pool_card : ((s.erase y) ∪ insert (p.vertices 3) a).card = 8 := by
  rw [card_union_of_disjoint h.triple_second_disjoint, h.first_triple_clique.card_eq,
    h.second_five_card]

lemma Configuration.ten_rows_card : ((insert p.leaf s) ∪ insert (p.vertices 3) a).card = 10 := by
  rw [card_union_of_disjoint (h.five_disjoint_core.mono_right h.second_five_subset),
    h.first_five_clique.card_eq, h.second_five_card]

lemma Configuration.matched_first_card {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    (FullLeafEquality.matchedFirst p s a y).card =
      contacts G (s.erase y) (insert (p.vertices 3) a) :=
  (FullLeafSparse.contacts_eq_positive_rows (h.matching_degrees hcard hn).1).symm

lemma Configuration.matched_second_card {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    (FullLeafEquality.matchedSecond p s a y).card =
      contacts G (s.erase y) (insert (p.vertices 3) a) := by
  rw [FullLeafEquality.matchedSecond,
    ← FullLeafSparse.contacts_eq_positive_rows (h.matching_degrees hcard hn).2, contacts_comm]

lemma Configuration.matching_contacts_le_three {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    contacts G (s.erase y) (insert (p.vertices 3) a) ≤ 3 := by
  rw [← h.matched_first_card hcard hn]
  exact (card_filter_le _ _).trans_eq h.first_triple_clique.card_eq

lemma Configuration.ten_row_split :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) (p.support ∪ s ∪ a) +
      ∑ j ∈ FullLeafEquality.further c s a,
        contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j =
      contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) univ := by
  have hsub : ({s, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr h.core)
  have he := c.contacts_selected_core_add_outside {s, a} hsub
    ((insert p.leaf s) ∪ insert (p.vertices 3) a)
  simpa only [biUnion_insert, singleton_biUnion, id_eq, ← h.paw, ← union_assoc,
    FullLeafEquality.further] using he

end Erdos577.FullLeafCore
