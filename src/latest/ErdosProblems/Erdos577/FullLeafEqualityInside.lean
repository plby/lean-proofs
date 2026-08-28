import ErdosProblems.Erdos577.FullLeafEqualityBlockBudget

/-! The exact inside ten-row sum, with only the five core degrees left to bound. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

omit [Fintype V] [DecidableRel G.Adj] h in
lemma core_split :
    p.triangle ∪ a = insert p.center (insert (p.vertices 2) (insert (p.vertices 3) a)) := by
  ext v
  simp only [Paw.triangle, Paw.center, mem_union, mem_insert, mem_singleton]
  tauto

lemma Configuration.core_card : (p.triangle ∪ a).card = 7 := by
  have hd := (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
  rw [card_union_of_disjoint hd, p.triangle_clique.card_eq, h.core_clique.card_eq]

lemma Configuration.centers_first_degree {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    degreeIn G p.center (insert p.leaf s) = 1 ∧
      degreeIn G (p.vertices 2) (insert p.leaf s) = 1 := by
  obtain ⟨hr, hb, _⟩ := h.preparation hcard hdeg hn
  have hbexact := (FullRow.unique_row_of_bound s (p.vertices 2) y h.exposed h.attached hb).1
  have huniq := (FullRow.unique_row_of_bound (p.triangle ∪ a) p.leaf p.center
    (mem_union_left _ p.center_mem_triangle) p.pendant
      (h.first_core_degree hcard hn (mem_insert_self _ _))).2
  have hnot : ¬G.Adj (p.vertices 2) p.leaf := by
    intro hh
    have he := (huniq (p.vertices 2) (mem_union_left _ (by simp [Paw.triangle]))).mp hh.symm
    exact p.edge12.ne he.symm
  rw [degreeIn_insert G p.center p.leaf h.leaf_out,
    if_pos (show G.Adj p.center p.leaf from p.pendant.symm),
    degreeIn_insert G (p.vertices 2) p.leaf h.leaf_out, if_neg hnot, hr, hbexact]
  exact ⟨rfl, rfl⟩

lemma Configuration.first_second_contacts {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    contacts G (insert p.leaf s) (insert (p.vertices 3) a) =
      contacts G (s.erase y) (insert (p.vertices 3) a) := by
  obtain ⟨hX, hY⟩ := h.marked_degrees_zero hcard hn
  rw [h.first_contacts, hX, hY, zero_add, zero_add]

lemma Configuration.first_core_contacts {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    contacts G (insert p.leaf s) (p.triangle ∪ a) =
      2 + contacts G (s.erase y) (insert (p.vertices 3) a) := by
  have hrout : p.center ∉ insert (p.vertices 2) (insert (p.vertices 3) a) := by
    rw [mem_insert, not_or]
    exact ⟨p.edge12.ne, fun hv ↦ (h.second_avoids hv).2.1 rfl⟩
  have hbout : p.vertices 2 ∉ insert (p.vertices 3) a :=
    fun hv ↦ (h.second_avoids hv).2.2 rfl
  obtain ⟨hr, hb⟩ := h.centers_first_degree hcard hdeg hn
  rw [contacts_comm G (insert p.leaf s) (p.triangle ∪ a), core_split, contacts,
    sum_insert hrout, sum_insert hbout, hr, hb]
  change 1 + (1 + contacts G (insert (p.vertices 3) a) (insert p.leaf s)) = _
  rw [contacts_comm G (insert (p.vertices 3) a) (insert p.leaf s),
    h.first_second_contacts hcard hn]
  omega

lemma Configuration.first_inside_contacts {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    contacts G (insert p.leaf s) (p.support ∪ s ∪ a) =
      22 + contacts G (s.erase y) (insert (p.vertices 3) a) := by
  rw [total_eq, contacts_union_right G (insert p.leaf s) h.five_disjoint_core,
    h.first_core_contacts hcard hdeg hn, contacts_self_eq_twice_edgeCount,
    edgeCount_clique h.first_five_clique.isClique, h.first_five_clique.card_eq]
  norm_num only [Nat.choose]
  omega

lemma Configuration.second_inside_contacts {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    contacts G (insert (p.vertices 3) a) (p.support ∪ s ∪ a) =
      contacts G (insert (p.vertices 3) a) (p.triangle ∪ a) +
        contacts G (s.erase y) (insert (p.vertices 3) a) := by
  rw [total_eq, contacts_union_right G (insert (p.vertices 3) a) h.five_disjoint_core,
    contacts_comm G (insert (p.vertices 3) a) (insert p.leaf s),
    h.first_second_contacts hcard hn, add_comm]

theorem Configuration.ten_inside_contacts {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) (p.support ∪ s ∪ a) =
      22 + 2 * contacts G (s.erase y) (insert (p.vertices 3) a) +
        contacts G (insert (p.vertices 3) a) (p.triangle ∪ a) := by
  rw [h.combined_contacts, h.first_inside_contacts hcard hdeg hn,
    h.second_inside_contacts hcard hn]
  omega

end Erdos577.FullLeafCore
