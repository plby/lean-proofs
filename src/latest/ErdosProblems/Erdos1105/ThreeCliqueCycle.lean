import ErdosProblems.Erdos1105.FewLowDegrees
import ErdosProblems.Erdos1105.PendantCounting
import ErdosProblems.Erdos1105.PathNeighborCounts

namespace Erdos1105

open SimpleGraph Finset

/-- A clique on `A ∪ T`, with all vertices of `A` also joined to every
remaining vertex. The even-path exceptional graph has `|T| = 3`. -/
def threeCliqueJoin {V : Type*} (A T : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (x ∈ A ∨ y ∈ A ∨ x ∈ T ∧ y ∈ T)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma degreeWithin_lower_of_all_adj {V : Type*} (G : SimpleGraph V)
    {S T : Finset V} (hTS : T ⊆ S) {x : V} (h : ∀ y ∈ T, G.Adj x y) :
    T.card ≤ degreeWithin G S x := by
  classical
  exact card_le_card (fun y hy ↦ mem_filter.mpr ⟨hTS hy, h y hy⟩)

/-- The exceptional join contains a cycle through `A`, the three-clique,
and `|A|-1` further vertices, even after deleting any one internal
edge of the three-clique. -/
theorem threeCliqueJoin_cycle_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    {A T B : Finset V} {l : ℕ} (hl : 2 ≤ l)
    (hAT : Disjoint A T) (hBA : Disjoint B A) (hBT : Disjoint B T)
    (hA : A.card = l - 1) (hT : T.card = 3) (hB : B.card = l - 2)
    (e : Sym2 V) (he : e.toFinset ⊆ T) :
    ∃ u, ∃ p : (threeCliqueJoin A T).Walk u u,
      p.IsCycle ∧ p.length = 2 * l ∧
      (∀ x, x ∈ p.support ↔ x ∈ A ∪ T ∪ B) ∧ e ∉ p.edges := by
  classical
  let G := threeCliqueJoin A T
  let D := G.deleteEdges {e}
  let S := A ∪ T ∪ B
  let J := D.induce (S : Set V)
  have hATB : Disjoint (A ∪ T) B := disjoint_union_left.mpr ⟨hBA.symm, hBT.symm⟩
  have hS : S.card = 2 * l := by
    dsimp only [S]
    rw [card_union_of_disjoint hATB, card_union_of_disjoint hAT, hA, hT, hB]
    omega
  have hAS : A ⊆ S := subset_union_left.trans subset_union_left
  have hTS : T ⊆ S := subset_union_right.trans subset_union_left
  have hBS : B ⊆ S := subset_union_right
  have hretain {x y : V} (hx : x ∉ T) (hxy : G.Adj x y) : D.Adj x y := by
    apply deleteEdges_adj.mpr
    refine ⟨hxy, ?_⟩
    intro hxe
    apply hx
    apply he
    rw [← hxe]
    simp
  have hdegA : ∀ x ∈ A, l ≤ degreeWithin D S x := by
    intro x hx
    have hxT : x ∉ T := fun h ↦ Finset.disjoint_left.mp hAT hx h
    have hd := degreeWithin_lower_of_all_adj D (erase_subset x S) (x := x) (by
      intro y hy
      exact hretain hxT ⟨(mem_erase.mp hy).1.symm, Or.inl hx⟩)
    rw [card_erase_of_mem (hAS hx), hS] at hd
    omega
  have hdegT : ∀ x ∈ T, l ≤ degreeWithin D S x := by
    intro x hx
    have hd := degreeWithin_lower_of_all_adj G (S := S)
      ((erase_subset x (A ∪ T)).trans subset_union_left) (x := x) (by
        intro y hy
        refine ⟨(mem_erase.mp hy).1.symm, ?_⟩
        rcases mem_union.mp (mem_erase.mp hy).2 with hyA | hyT
        · exact Or.inr (Or.inl hyA)
        · exact Or.inr (Or.inr ⟨hx, hyT⟩))
    rw [card_erase_of_mem (mem_union_right A hx), card_union_of_disjoint hAT, hA, hT] at hd
    have hd' := degreeWithin_delete_edge_lower G S x e
    change degreeWithin G S x ≤ degreeWithin D S x + 1 at hd'
    omega
  have hmin : ∀ x ∈ S, l - 1 ≤ degreeWithin D S x := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact (by omega : l - 1 ≤ l).trans (hdegA x hxA)
    by_cases hxT : x ∈ T
    · exact (by omega : l - 1 ≤ l).trans (hdegT x hxT)
    rw [← hA]
    apply degreeWithin_lower_of_all_adj D hAS
    intro y hy
    exact hretain hxT ⟨fun h ↦ hxA (h ▸ hy), Or.inr (Or.inl hy)⟩
  let L := B.subtype (fun x ↦ x ∈ S)
  have hL : L.card = l - 2 := by
    dsimp only [L]
    rw [card_subtype, filter_eq_self.mpr hBS, hB]
  have hn : Fintype.card (S : Set V) = 2 * l :=
    (Fintype.card_of_finset' S (fun _ ↦ Iff.rfl)).trans hS
  have hham : J.IsHamiltonian := by
    apply hamiltonian_of_few_low_degrees J hl hn L (by omega)
    · intro x
      rw [← degreeWithin_eq_induce_degree D S x]
      exact hmin x.val x.property
    · intro x hx
      have hxB : x.val ∉ B := fun h ↦ hx (mem_subtype.mpr h)
      rw [← degreeWithin_eq_induce_degree D S x]
      rcases mem_union.mp x.property with h | h
      · exact (mem_union.mp h).elim (hdegA x.val) (hdegT x.val)
      · exact (hxB h).elim
  obtain ⟨u, p, hp⟩ := hham (by omega)
  let φ : J →g G := ⟨Subtype.val, fun h ↦ (deleteEdges_adj.mp h).1⟩
  refine ⟨u.val, p.map φ, hp.isCycle.map Subtype.val_injective, ?_, ?_, ?_⟩
  · rw [Walk.length_map, hp.length_eq, hn]
  · intro x
    rw [Walk.support_map]
    constructor
    · intro hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact v.property
    · intro hx
      exact List.mem_map.mpr ⟨⟨x, hx⟩, hp.mem_support _, rfl⟩
  · intro he'
    rw [Walk.edges_map] at he'
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he'
    have hadj := p.edges_subset_edgeSet hf
    induction f using Sym2.inductionOn with
    | _ x y =>
      have hxy : D.Adj x.val y.val := hadj
      exact (deleteEdges_adj.mp hxy).2 hfe

end Erdos1105

#print axioms Erdos1105.threeCliqueJoin_cycle_avoiding
