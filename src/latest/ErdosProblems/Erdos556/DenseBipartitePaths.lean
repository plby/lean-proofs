import ErdosProblems.Erdos556.BipartiteDefect

/-! Exact paths with prescribed endpoints in a dense bipartite pair. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_even_path_of_bipartite_defect {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L d : ℕ) (hL : 0 < L)
    (X Y : Finset V) (hdis : Disjoint X Y) (hdef : BipartiteDefect G X Y d)
    (hX : L + 2 * d + 1 ≤ X.card) (hY : L + 2 * d ≤ Y.card)
    (u v : V) (hu : u ∈ X) (hv : v ∈ X) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = 2 * L ∧ ∀ z ∈ p.support, z ∈ X ∪ Y := by
  induction L generalizing X Y u v with
  | zero => omega
  | succ L ih =>
      classical
      by_cases hzero : L = 0
      · subst L
        obtain ⟨y, hy, huy, hvy⟩ := exists_common_neighbor_of_defect G u v Y d
          (hdef.left u hu) (hdef.left v hv) (by omega)
        let p : G.Walk u v := Walk.cons huy (Walk.cons hvy.symm Walk.nil)
        have huY : u ∉ Y := Finset.disjoint_left.mp hdis hu
        refine ⟨p, ?_, rfl, ?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨Walk.IsPath.of_adj hvy.symm, ?_⟩
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false, not_or]
          exact ⟨fun h => huY (h ▸ hy), huv⟩
        · intro z hz
          simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with h | h | h
          · exact h ▸ mem_union_left Y hu
          · exact h ▸ mem_union_right X hy
          · exact h ▸ mem_union_left Y hv
      · obtain ⟨y, hy, _, huy⟩ := exists_neighbor_avoiding_of_defect G u Y ∅ d
          (hdef.left u hu) (by simp only [card_empty]; omega)
        have hpair : ({u, v} : Finset V).card ≤ 2 := by
          have h := card_insert_le u ({v} : Finset V)
          simp only [card_singleton] at h
          omega
        obtain ⟨x, hx, hxf, hyx⟩ := exists_neighbor_avoiding_of_defect G y X {u, v} d
          (hdef.right y hy) (by omega)
        have hxu : x ≠ u := fun h => hxf (by simp [h])
        have hxv : x ≠ v := fun h => hxf (by simp [h])
        have hx' : x ∈ X.erase u := mem_erase.mpr ⟨hxu, hx⟩
        have hv' : v ∈ X.erase u := mem_erase.mpr ⟨huv.symm, hv⟩
        have hX' : L + 2 * d + 1 ≤ (X.erase u).card := by rw [card_erase_of_mem hu]; omega
        have hY' : L + 2 * d ≤ (Y.erase y).card := by rw [card_erase_of_mem hy]; omega
        obtain ⟨q, hq, hqL, hqS⟩ := ih (by omega) (X.erase u) (Y.erase y)
          (hdis.mono (erase_subset _ _) (erase_subset _ _))
          (hdef.mono (erase_subset _ _) (erase_subset _ _)) hX' hY' x v hx' hv' hxv
        have huq : u ∉ q.support := by
          intro h
          rcases mem_union.mp (hqS u h) with h | h
          · exact (mem_erase.mp h).1 rfl
          · exact (Finset.disjoint_left.mp hdis hu) (mem_of_mem_erase h)
        have hyq : y ∉ q.support := by
          intro h
          rcases mem_union.mp (hqS y h) with h | h
          · exact (Finset.disjoint_left.mp hdis (mem_of_mem_erase h)) hy
          · exact (mem_erase.mp h).1 rfl
        have huyne : u ≠ y := fun h => (Finset.disjoint_left.mp hdis hu) (h ▸ hy)
        let p : G.Walk u v := Walk.cons huy (Walk.cons hyx q)
        refine ⟨p, ?_, ?_, ?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hq, hyq⟩, ?_⟩
          simpa only [Walk.support_cons, List.mem_cons, not_or] using ⟨huyne, huq⟩
        · simp only [p, Walk.length_cons, hqL]
          omega
        · intro z hz
          simp only [p, Walk.support_cons, List.mem_cons] at hz
          rcases hz with h | h | h
          · exact h ▸ mem_union_left Y hu
          · exact h ▸ mem_union_right X hy
          · exact (union_subset_union (erase_subset _ _) (erase_subset _ _)) (hqS z h)

theorem exists_odd_path_of_bipartite_defect {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L d : ℕ) (hL : 2 ≤ L)
    (X Y : Finset V) (hdis : Disjoint X Y) (hdef : BipartiteDefect G X Y d)
    (hX : L + 2 * d ≤ X.card) (hY : L + 2 * d ≤ Y.card)
    (u v : V) (hu : u ∈ X) (hv : v ∈ Y) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = 2 * L - 1 ∧ ∀ z ∈ p.support, z ∈ X ∪ Y := by
  classical
  obtain ⟨x, hx, hxu, hvx⟩ := exists_neighbor_avoiding_of_defect G v X {u} d
    (hdef.right v hv) (by simp only [card_singleton]; omega)
  have hux : u ≠ x := by
    intro h
    exact hxu (by simp [h])
  have hY' : L - 1 + 2 * d ≤ (Y.erase v).card := by rw [card_erase_of_mem hv]; omega
  obtain ⟨q, hq, hqL, hqS⟩ := exists_even_path_of_bipartite_defect G (L - 1) d (by omega)
    X (Y.erase v) (hdis.mono_right (erase_subset _ _))
    (hdef.mono Subset.rfl (erase_subset _ _)) (by omega) hY' u x hu hx hux
  have hvq : v ∉ q.support := by
    intro h
    rcases mem_union.mp (hqS v h) with h | h
    · exact (Finset.disjoint_left.mp hdis h) hv
    · exact (mem_erase.mp h).1 rfl
  refine ⟨q.concat hvx.symm, hq.concat hvq hvx.symm, ?_, ?_⟩
  · rw [Walk.length_concat, hqL]
    omega
  · intro z hz
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with h | h
    · exact (union_subset_union Subset.rfl (erase_subset _ _)) (hqS z h)
    · exact h ▸ mem_union_right X hv

#print axioms exists_even_path_of_bipartite_defect
#print axioms exists_odd_path_of_bipartite_defect

end Erdos556
