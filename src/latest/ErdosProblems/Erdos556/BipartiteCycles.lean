import ErdosProblems.Erdos556.BipartitePaths

/-!
# Exact paths and cycles in complete bipartite pairs
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_odd_path_of_complete_bipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L : ℕ) (hL : 0 < L) (X Y : Finset V)
    (hXY : Disjoint X Y) (hcomplete : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hX : L ≤ X.card) (hY : L ≤ Y.card)
    (u v : V) (hu : u ∈ X) (hv : v ∈ Y) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = 2 * L - 1 ∧
      ∀ z ∈ p.support, z ∈ X ∪ Y := by
  classical
  by_cases hL1 : L = 1
  · subst L
    let p := (hcomplete u hu v hv).toWalk
    refine ⟨p, Walk.IsPath.of_adj _, rfl, ?_⟩
    intro z hz
    have hz' : z = u ∨ z = v := by simpa [p, SimpleGraph.Adj.toWalk] using hz
    exact hz'.elim (fun h => h ▸ mem_union_left _ hu) (fun h => h ▸ mem_union_right _ hv)
  · have hex : (X.erase u).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hu]
      omega
    obtain ⟨x, hx⟩ := hex
    have hxX := mem_of_mem_erase hx
    have hux : u ≠ x := (mem_erase.mp hx).1.symm
    have hY' : L - 1 ≤ (Y.erase v).card := by rw [card_erase_of_mem hv]; omega
    obtain ⟨q, hq, hqL, hqS⟩ := exists_even_path_of_complete_bipartite G (L - 1) (by omega)
      X (Y.erase v) (hXY.mono_right (erase_subset _ _))
      (fun a ha b hb => hcomplete a ha b (mem_of_mem_erase hb)) (by omega) hY' u x hu hxX hux
    have hvq : v ∉ q.support := by
      intro hvq
      rcases mem_union.mp (hqS v hvq) with hvX | hvY
      · exact Finset.disjoint_left.mp hXY hvX hv
      · exact (mem_erase.mp hvY).1 rfl
    refine ⟨q.concat (hcomplete x hxX v hv), hq.concat hvq _, ?_, ?_⟩
    · rw [Walk.length_concat, hqL]
      omega
    · intro z hz
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
      rcases hz with hzq | hzv
      · exact (union_subset_union (Subset.refl X) (erase_subset _ _)) (hqS z hzq)
      · exact hzv ▸ mem_union_right X hv

theorem exists_even_cycle_of_complete_bipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L : ℕ) (hL : 2 ≤ L) (X Y : Finset V)
    (hXY : Disjoint X Y) (hcomplete : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hX : L ≤ X.card) (hY : L ≤ Y.card) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = 2 * L ∧
      ∀ z ∈ c.support, z ∈ X ∪ Y := by
  classical
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < X.card by omega)
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < Y.card by omega)
  obtain ⟨p, hp, hpL, hpS⟩ := exists_odd_path_of_complete_bipartite G L (by omega) X Y
    hXY hcomplete hX hY u v hu hv
  let q := (hcomplete u hu v hv).toWalk
  have hq : q.IsPath := Walk.IsPath.of_adj _
  have hqS (z : V) (hz : z ∈ q.support) : z = u ∨ z = v := by
    simpa [q, SimpleGraph.Adj.toWalk] using hz
  refine ⟨u, p.append q.reverse,
    isCycle_append_reverse_of_support_inter p q hp hq (by omega) (fun z _ hz => hqS z hz), ?_, ?_⟩
  · simp only [Walk.length_append, Walk.length_reverse, q, SimpleGraph.Adj.toWalk,
      Walk.length_cons, Walk.length_nil, hpL]
    omega
  · intro z hz
    rcases (Walk.mem_support_append_iff p q.reverse).mp hz with hzp | hzq
    · exact hpS z hzp
    · have hzq' : z ∈ q.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hzq
      rcases hqS z hzq' with hzu | hzv
      · exact hzu ▸ mem_union_left _ hu
      · exact hzv ▸ mem_union_right _ hv

#print axioms exists_odd_path_of_complete_bipartite
#print axioms exists_even_cycle_of_complete_bipartite

end Erdos556
