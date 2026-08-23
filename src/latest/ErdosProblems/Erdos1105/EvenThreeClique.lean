import ErdosProblems.Erdos1105.ThreeCliqueCycle
import ErdosProblems.Erdos1105.RainbowCycleExtension

namespace Erdos1105

open SimpleGraph Finset

/-- The even-path exceptional graph `H(n,2*l+1,l-1)` cannot be a
rainbow subgraph of a complete coloring without a rainbow `P_(2*l+2)`.
This includes the smallest even case, `l = 2`. -/
theorem rainbow_path_of_threeCliqueJoin {V C : Type*} [Fintype V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {R : SimpleGraph V}
    (hR : Set.InjOn (extendColor c) R.edgeSet) {A T : Finset V} {l : ℕ}
    (hl : 2 ≤ l) (hn : 2 * l + 2 ≤ Fintype.card V)
    (hAT : Disjoint A T) (hA : A.card = l - 1) (hT : T.card = 3)
    (hjoin : threeCliqueJoin A T ≤ R) :
    ∃ f : (pathGraph (2 * l + 2)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
  classical
  let G := threeCliqueJoin A T
  have hG : Set.InjOn (extendColor c) G.edgeSet :=
    hR.mono (edgeSet_mono hjoin)
  have hU : l ≤ (A ∪ T)ᶜ.card := by
    rw [card_compl, card_union_of_disjoint hAT, hA, hT]
    omega
  obtain ⟨Y, hYU, hY⟩ := exists_subset_card_eq hU
  obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < Y.card)
  have hYy : (Y.erase y).card = l - 1 := by rw [card_erase_of_mem hy, hY]
  obtain ⟨z, hz⟩ := card_pos.mp (by omega : 0 < (Y.erase y).card)
  have hzy : z ≠ y := (mem_erase.mp hz).1
  let B := (Y.erase y).erase z
  have hB : B.card = l - 2 := by
    dsimp only [B]
    rw [card_erase_of_mem hz, hYy]
    omega
  have hBY : B ⊆ Y := (erase_subset _ _).trans (erase_subset _ _)
  have hYA (x : V) (hx : x ∈ Y) : x ∉ A := by
    have := mem_compl.mp (hYU hx)
    exact fun h ↦ this (mem_union_left T h)
  have hYT (x : V) (hx : x ∈ Y) : x ∉ T := by
    have := mem_compl.mp (hYU hx)
    exact fun h ↦ this (mem_union_right A h)
  have hBA : Disjoint B A := Finset.disjoint_left.mpr (fun x hx ↦ hYA x (hBY hx))
  have hBT : Disjoint B T := Finset.disjoint_left.mpr (fun x hx ↦ hYT x (hBY hx))
  have hex : ∃ e : Sym2 V, e.toFinset ⊆ T ∧
      ∀ f ∈ G.edgeSet, f.toFinset ⊆ T →
        extendColor c f = extendColor c s(z, y) → f = e := by
    by_cases h : ∃ e ∈ G.edgeSet, e.toFinset ⊆ T ∧
        extendColor c e = extendColor c s(z, y)
    · obtain ⟨e, he, hsub, hc⟩ := h
      exact ⟨e, hsub, fun f hf _ hfc ↦ hG hf he (hfc.trans hc.symm)⟩
    · obtain ⟨t, ht⟩ := card_pos.mp (by omega : 0 < T.card)
      refine ⟨s(t, t), ?_, ?_⟩
      · simpa only [Sym2.toFinset_mk_eq, insert_eq_of_mem (mem_singleton_self t)] using
          singleton_subset_iff.mpr ht
      · intro f hf hsub hc
        exact (h ⟨f, hf, hsub, hc⟩).elim
  obtain ⟨e, he, hecolor⟩ := hex
  obtain ⟨u, p, hp, hlen, hsupp, havoid⟩ :=
    threeCliqueJoin_cycle_avoiding hl hAT hBA hBT hA hT hB e he
  have hynew : y ∉ p.support := by
    rw [hsupp]
    simp only [mem_union, not_or]
    refine ⟨⟨hYA y hy, hYT y hy⟩, ?_⟩
    intro h
    exact (mem_erase.mp (mem_erase.mp h).2).1 rfl
  have hzY : z ∈ Y := (mem_erase.mp hz).2
  have hznew : z ∉ p.support := by
    rw [hsupp]
    simp only [mem_union, not_or]
    refine ⟨⟨hYA z hzY, hYT z hzY⟩, ?_⟩
    intro h
    exact (mem_erase.mp h).1 rfl
  have hcover : ∀ d ∈ p.darts, extendColor c d.edge = extendColor c s(z, y) →
      d.fst ∈ (A : Set V) ∨ d.snd ∈ (A : Set V) := by
    intro d hd hc
    have hadj : G.Adj d.fst d.snd := d.adj
    rcases hadj.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have hsub : d.edge.toFinset ⊆ T := by
        intro x hx
        have hx : x = d.fst ∨ x = d.snd := by
          simpa only [Dart.edge, Sym2.mem_toFinset, Sym2.mem_iff] using hx
        rcases hx with rfl | rfl
        · exact h.1
        · exact h.2
      have heq := hecolor d.edge d.adj hsub hc
      exact (havoid (heq ▸ List.mem_map.mpr ⟨d, hd, rfl⟩)).elim
  have hAnonempty : (A : Set V).Nonempty := by
    obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < A.card)
    exact ⟨a, ha⟩
  have h := rainbow_path_of_cycle_two_attached c hG p hp (A : Set V)
    (fun x hx ↦ (hsupp x).mpr (mem_union_left B (mem_union_left T hx)))
    hAnonempty hynew hznew hzy.symm
    (fun x hx ↦ ⟨fun h ↦ hYA y hy (h ▸ hx), Or.inr (Or.inl hx)⟩)
    (fun x hx ↦ ⟨fun h ↦ hYA z hzY (h ▸ hx), Or.inr (Or.inl hx)⟩) hcover
  rwa [hlen] at h

end Erdos1105

#print axioms Erdos1105.rainbow_path_of_threeCliqueJoin
