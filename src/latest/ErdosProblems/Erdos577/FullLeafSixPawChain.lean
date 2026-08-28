import ErdosProblems.Erdos577.FullLeafSixSets

/-! Every first matching endpoint has an actual strong paw with the second triangle. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.matched_paw_chain (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ s.erase y) :
    ∃ (e : TriangleChain G) (q : Paw G), e.Strong ∧ q.support = e.remainder ∧
      q.leaf = u ∧ q.triangle = FullLeafEquality.matchedSecond p s a y ∧
      e.terminal = u ∧ e.triangle = FullLeafEquality.matchedSecond p s a y ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      insert p.leaf (s.erase u) ∈ e.blocks ∧
      (p.triangle ∪ a) \ FullLeafEquality.matchedSecond p s a y ∈ e.blocks ∧
      ∀ j ∈ c.blocks, j ≠ s → j ≠ a → j ∈ e.blocks := by
  let t := FullLeafEquality.matchedSecond p s a y
  let a' := (p.triangle ∪ a) \ t
  have ht : G.IsNClique 3 t := hm.matched_second_triangle hcard hdeg hn
  have ha' : G.IsNClique 4 a' := hm.matched_core_complement hcard hdeg hn
  have huFirst : u ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hu).2
  have huK : u ∉ p.triangle ∪ a := fun hh ↦
    disjoint_left.mp hm.1.five_disjoint_core huFirst hh
  have hut : u ∉ t := fun hh ↦ huK (hm.1.matched_second_subset hh)
  obtain ⟨v, hv, huv⟩ := hm.first_matched_neighbor hcard hdeg hn hu
  have hpos : 0 < degreeIn G u t := card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, huv⟩⟩
  obtain ⟨q, hqu, hqt⟩ := Paw.exists_of_triangle ht hut hpos
  obtain ⟨d, hd, hdu, hdt, hde, hdc, hdb⟩ :=
    FullRow.exists_full_leaf_swap hm.1.feasible p hm.1.paw hm.1.first hm.1.full
      u (mem_erase.mp hu).2
  have had : a ∈ d.blocks := by
    rw [hdb]
    exact mem_union_left _ (mem_erase.mpr ⟨hm.1.different, hm.1.core⟩)
  have hcover : t ∪ a' = p.triangle ∪ a := union_sdiff_of_subset hm.1.matched_second_subset
  let loc : LocalChain G (d.remainder ∪ a) := {
    terminal := u
    triangle := t
    block := a'
    triangle_clique := ht
    terminal_not_mem := hut
    quad := QuadOn.of_clique ha'.card_eq ha'.isClique
    disjoint := disjoint_insert_left.mpr
      ⟨fun hh ↦ huK (mem_sdiff.mp hh).1, disjoint_sdiff_self_right⟩
    cover := by
      change insert u t ∪ a' = insert d.terminal d.triangle ∪ a
      rw [insert_union, hcover, hdu, hdt, insert_union] }
  have hscore : edgeCount G loc.block = edgeCount G a := by
    change edgeCount G a' = edgeCount G a
    rw [edgeCount_clique ha'.isClique, edgeCount_clique hm.1.core_clique.isClique,
      ha'.card_eq, hm.1.core_clique.card_eq]
  let e := d.replaceBlock a had loc
  have he : e.Feasible := hd.replaceBlock_feasible had loc hscore
  have hscores := d.replaceBlock_scores_eq had loc hscore
  have hbound := e.terminal_degree_le_one hcard hn
  have hstrong : e.Strong := by
    refine ⟨he, ?_⟩
    change degreeIn G u t = 1
    change degreeIn G u t ≤ 1 at hbound
    omega
  have hsupport : q.support = e.remainder := by
    rw [q.support_eq, hqu, hqt]
    rfl
  have hXa : p.leaf ∉ a := fun hh ↦ disjoint_left.mp (hm.1.paw_disjoint hm.1.core)
    (p.support_eq ▸ mem_insert_self _ _) hh
  have hfirstNe : insert p.leaf (s.erase u) ≠ a := fun hh ↦ hXa (hh ▸ mem_insert_self _ _)
  have hfirstd : insert p.leaf (s.erase u) ∈ d.blocks := by
    rw [hdb]
    exact mem_union_right _ (mem_singleton_self _)
  refine ⟨e, q, hstrong, hsupport, hqu, hqt, rfl, rfl,
    hscores.1.trans hde, hscores.2.trans hdc, ?_, ?_, ?_⟩
  · exact mem_union_left _ (mem_erase.mpr ⟨hfirstNe, hfirstd⟩)
  · exact mem_union_right _ (mem_singleton_self _)
  · intro j hj hjs hja
    apply mem_union_left
    apply mem_erase.mpr
    refine ⟨hja, ?_⟩
    rw [hdb]
    exact mem_union_left _ (mem_erase.mpr ⟨hjs, hj⟩)

end Erdos577.FullLeafCore
