import ErdosProblems.Erdos556.ClosingPaths

/-!
# Prescribed even paths in a complete bipartite reservoir

Two distinct vertices on one side can be joined by a simple path of any
permitted positive even length. The proof removes its first two vertices
and applies induction, keeping the support inside the two sides.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_even_path_of_complete_bipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L : ℕ) (hL : 0 < L) (X Y : Finset V)
    (hXY : Disjoint X Y) (hcomplete : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hX : L + 1 ≤ X.card) (hY : L ≤ Y.card)
    (u v : V) (hu : u ∈ X) (hv : v ∈ X) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = 2 * L ∧
      ∀ z ∈ p.support, z ∈ X ∪ Y := by
  induction L generalizing X Y u v with
  | zero => omega
  | succ L ih =>
      classical
      obtain ⟨y, hy⟩ := card_pos.mp (show 0 < Y.card by omega)
      have huy : u ≠ y := fun h => Finset.disjoint_left.mp hXY hu (h.symm ▸ hy)
      have hvy : v ≠ y := fun h => Finset.disjoint_left.mp hXY hv (h.symm ▸ hy)
      by_cases hzero : L = 0
      · subst L
        let p : G.Walk u v := Walk.cons (hcomplete u hu y hy)
          (Walk.cons (hcomplete v hv y hy).symm Walk.nil)
        refine ⟨p, ?_, rfl, ?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨?_, ?_⟩, ?_⟩
          · exact Walk.IsPath.nil
          · simpa using hvy.symm
          · simpa only [Walk.support_cons, Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false, not_or] using And.intro huy huv
        · intro z hz
          simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact mem_union_left _ hu
          · exact mem_union_right _ hy
          · exact mem_union_left _ hv
      · have hwex : (X \ {u, v}).Nonempty := by
          apply card_pos.mp
          have hle : ({u, v} : Finset V).card ≤ 2 := by
            exact (card_insert_le _ _).trans (by simp)
          have hc := card_le_card (show X ∩ {u, v} ⊆ ({u, v} : Finset V) from inter_subset_right)
          rw [card_sdiff, inter_comm]
          omega
        obtain ⟨w, hw⟩ := hwex
        have hwX : w ∈ X := (mem_sdiff.mp hw).1
        have hwu : w ≠ u := fun h => (mem_sdiff.mp hw).2 (by simp [h])
        have hwv : w ≠ v := by
          have hn := (mem_sdiff.mp hw).2
          exact fun h => hn (by simp [h])
        have hX' : L + 1 ≤ (X.erase u).card := by rw [card_erase_of_mem hu]; omega
        have hY' : L ≤ (Y.erase y).card := by rw [card_erase_of_mem hy]; omega
        have hXY' : Disjoint (X.erase u) (Y.erase y) :=
          hXY.mono (erase_subset _ _) (erase_subset _ _)
        have hcomplete' : ∀ x ∈ X.erase u, ∀ z ∈ Y.erase y, G.Adj x z :=
          fun x hx z hz => hcomplete x (mem_of_mem_erase hx) z (mem_of_mem_erase hz)
        obtain ⟨q, hq, hqlen, hqS⟩ := ih (by omega) (X.erase u) (Y.erase y) hXY'
          hcomplete' hX' hY' w v (mem_erase.mpr ⟨hwu, hwX⟩)
          (mem_erase.mpr ⟨huv.symm, hv⟩) hwv
        have huq : u ∉ q.support := by
          intro h
          rcases mem_union.mp (hqS u h) with hx | hz
          · exact (mem_erase.mp hx).1 rfl
          · exact Finset.disjoint_left.mp hXY hu (mem_of_mem_erase hz)
        have hyq : y ∉ q.support := by
          intro h
          rcases mem_union.mp (hqS y h) with hx | hz
          · exact Finset.disjoint_left.mp hXY (mem_of_mem_erase hx) hy
          · exact (mem_erase.mp hz).1 rfl
        let p : G.Walk u v := Walk.cons (hcomplete u hu y hy)
          (Walk.cons (hcomplete w hwX y hy).symm q)
        refine ⟨p, ?_, ?_, ?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hq, hyq⟩, ?_⟩
          simpa only [Walk.support_cons, List.mem_cons, not_or] using And.intro huy huq
        · simp only [p, Walk.length_cons, hqlen]
          omega
        · intro z hz
          simp only [p, Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | rfl | hz
          · exact mem_union_left _ hu
          · exact mem_union_right _ hy
          · exact (union_subset_union (erase_subset _ _) (erase_subset _ _)) (hqS z hz)

#print axioms exists_even_path_of_complete_bipartite

theorem exists_cycle_of_bipartite_reservoir {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L : ℕ) (hL : 0 < L) (X Y : Finset V)
    (hXY : Disjoint X Y) (hcomplete : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hX : L + 1 ≤ X.card) (hY : L ≤ Y.card)
    (u v : V) (hu : u ∈ X) (hv : v ∈ X) (huv : u ≠ v)
    (p : G.Walk u v) (hp : p.IsPath) (hlen : 1 < p.length)
    (hoff : ∀ z ∈ p.support, z ∈ X ∪ Y → z = u ∨ z = v) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = p.length + 2 * L := by
  obtain ⟨q, hq, hqL, hqS⟩ := exists_even_path_of_complete_bipartite G L hL X Y
    hXY hcomplete hX hY u v hu hv huv
  refine ⟨p.append q.reverse, ?_, ?_⟩
  · exact isCycle_append_reverse_of_support_inter p q hp hq hlen
      (fun z hzp hzq => hoff z hzp (hqS z hzq))
  · simp only [Walk.length_append, Walk.length_reverse, hqL]

#print axioms exists_cycle_of_bipartite_reservoir

end Erdos556
