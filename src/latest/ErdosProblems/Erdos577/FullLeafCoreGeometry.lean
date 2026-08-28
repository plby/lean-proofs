import ErdosProblems.Erdos577.FullLeafCoreSwap

/-! Cardinalities, matching uniqueness, and the unchanged outside blocks under the interchange. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.total_card : (p.support ∪ s ∪ a).card = 12 := by
  have hd : Disjoint (p.support ∪ s) a := disjoint_union_left.mpr ⟨h.paw_disjoint h.core,
    c.property.blocks_disjoint h.first h.core h.different.symm⟩
  rw [card_union_of_disjoint hd, card_union_of_disjoint (h.paw_disjoint h.first),
    p.card_support, h.first_clique.card_eq, h.core_clique.card_eq]

omit [Fintype V] [DecidableRel G.Adj] h in
lemma total_eq : p.support ∪ s ∪ a = (insert p.leaf s) ∪ (p.triangle ∪ a) := by
  rw [p.support_eq]
  ext v
  simp only [mem_union, mem_insert]
  tauto

lemma Configuration.swapped_total {p' : Paw G} (hleaf : p'.leaf = y)
    (htri : p'.triangle = p.triangle) :
    p'.support ∪ insert p.leaf (s.erase y) ∪ a = p.support ∪ s ∪ a := by
  rw [p'.support_eq, p.support_eq, hleaf, htri]
  ext v
  have hyv : v = y → v ∈ s := fun hh ↦ hh ▸ h.exposed
  simp only [mem_union, mem_insert, mem_erase]
  tauto

lemma Configuration.swapped_outside_blocks {e : TriangleChain G}
    (he : e.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase y)}) (j : Finset V) :
    (j ∈ c.blocks ∧ j ≠ s ∧ j ≠ a) ↔
      (j ∈ e.blocks ∧ j ≠ insert p.leaf (s.erase y) ∧ j ≠ a) := by
  constructor
  · rintro ⟨hj, hjs, hja⟩
    have hjnew : j ≠ insert p.leaf (s.erase y) := by
      intro hh
      exact disjoint_left.mp (h.paw_disjoint hj) (p.support_eq ▸ mem_insert_self _ _)
        (hh.symm ▸ mem_insert_self _ _)
    refine ⟨?_, hjnew, hja⟩
    rw [he]
    exact mem_union_left _ (mem_erase.mpr ⟨hjs, hj⟩)
  · rintro ⟨hj, hjnew, hja⟩
    rw [he] at hj
    rcases mem_union.mp hj with hj | hj
    · exact ⟨(mem_erase.mp hj).2, (mem_erase.mp hj).1, hja⟩
    · exact False.elim (hjnew (mem_singleton.mp hj))

theorem Configuration.matching_unique {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) :
    (∀ x ∈ s.erase y, ∀ u ∈ insert (p.vertices 3) a, ∀ v ∈ insert (p.vertices 3) a,
      G.Adj x u → G.Adj x v → u = v) ∧
    (∀ u ∈ insert (p.vertices 3) a, ∀ x ∈ s.erase y, ∀ z ∈ s.erase y,
      G.Adj x u → G.Adj z u → x = z) := by
  obtain ⟨hleft, hright⟩ := h.matching_degrees hcard hn
  constructor
  · intro x hx u hu v hv hxu hxv
    exact ((FullRow.unique_row_of_bound _ x u hu hxu (hleft x hx)).2 v hv).mp hxv |>.symm
  · intro u hu x hx z hz hxu hzu
    exact ((FullRow.unique_row_of_bound _ u x hx hxu.symm (hright u hu)).2 z hz).mp hzu.symm
      |>.symm

end Erdos577.FullLeafCore
