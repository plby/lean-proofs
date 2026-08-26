import ErdosProblems.Erdos556.BipartiteOddCycle
import ErdosProblems.Erdos556.JoinedCorePaths

/-! Assigning every outside vertex to a clique core to which it is completely joined. -/

namespace Erdos556

open SimpleGraph Finset

theorem outside_vertex_complete_to_one_core {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hdis : Disjoint A B) (hA : r ≤ A.card) (hB : r ≤ B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, Gᶜ.Adj a b)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ)
    (x : V) (hxA : x ∉ A) (hxB : x ∉ B) :
    (∀ a ∈ A, G.Adj x a) ∨ (∀ b ∈ B, G.Adj x b) := by
  classical
  by_contra h
  push Not at h
  obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩ := h
  have hxa' : Gᶜ.Adj x a := by
    rw [compl_adj]
    exact ⟨fun he => hxA (he ▸ ha), hxa⟩
  have hxb' : Gᶜ.Adj x b := by
    rw [compl_adj]
    exact ⟨fun he => hxB (he ▸ hb), hxb⟩
  exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
    (exists_odd_cycle_of_bipartite_outside_vertex Gᶜ A B r hr hdis hA hB hcross
      x a b hxA hxB ha hb hxa' hxb'))

theorem exists_joined_core_buckets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hdis : Disjoint A B) (hAc : r ≤ A.card) (hBc : r ≤ B.card)
    (hA : G.IsClique (A : Set V)) (hB : G.IsClique (B : Set V))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, Gᶜ.Adj a b)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) :
    ∃ S T : Finset V, Disjoint S T ∧ S ∪ T = univ ∧ A ⊆ S ∧ B ⊆ T ∧
      (∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s) ∧
      (∀ b ∈ B, ∀ t ∈ T, b ≠ t → G.Adj b t) := by
  classical
  let X := univ.filter (fun x => x ∉ B ∧ ∀ a ∈ A, G.Adj x a)
  let S := A ∪ X
  let T := Sᶜ
  have hAS : A ⊆ S := subset_union_left
  have hBS : ∀ b ∈ B, b ∉ S := by
    intro b hb hbs
    rcases mem_union.mp hbs with hbA | hbX
    · exact (Finset.disjoint_left.mp hdis hbA) hb
    · exact (mem_filter.mp hbX).2.1 hb
  have hBT : B ⊆ T := fun b hb => mem_compl.mpr (hBS b hb)
  refine ⟨S, T, disjoint_compl_right, union_compl S, hAS, hBT, ?_, ?_⟩
  · intro a ha s hs has
    rcases mem_union.mp hs with hsA | hsX
    · exact hA ha hsA has
    · exact ((mem_filter.mp hsX).2.2 a ha).symm
  · intro b hb t ht hbt
    have htS : t ∉ S := mem_compl.mp ht
    by_cases htB : t ∈ B
    · exact hB hb htB hbt
    · have htA : t ∉ A := fun h => htS (hAS h)
      rcases outside_vertex_complete_to_one_core G A B r hr hdis hAc hBc hcross hno
        t htA htB with h | h
      · have htX : t ∈ X := mem_filter.mpr ⟨mem_univ _, htB, h⟩
        exact (htS (mem_union_right A htX)).elim
      · exact (h b hb).symm

#print axioms exists_joined_core_buckets

end Erdos556
