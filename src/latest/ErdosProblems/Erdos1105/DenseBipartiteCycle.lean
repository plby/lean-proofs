import ErdosProblems.Erdos1105.DenseBipartite

namespace Erdos1105

open SimpleGraph Finset

/-- The dense bipartite Hamilton-cycle lemma localized to its two
parts; vertices outside the parts need not be removed by the caller. -/
theorem cycle_of_dense_bipartite_parts {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hA : 2 ≤ A.card) (hcard : A.card = B.card)
    (hedges : (A.card - 1) * A.card + 2 ≤ G.edgeFinset.card) :
    ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 2 * A.card ∧
      ∀ x, x ∈ p.support ↔ x ∈ A ∪ B := by
  classical
  let S := A ∪ B
  let L := A.subtype (fun x ↦ x ∈ S)
  let M := B.subtype (fun x ↦ x ∈ S)
  let J := G.induce (S : Set V)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    exact fun x hx hy ↦ Set.disjoint_left.mp hAB.disjoint hx hy
  have hS : S.card = 2 * A.card := by
    dsimp only [S]
    rw [card_union_of_disjoint hdisj, ← hcard]
    omega
  have hL : L.card = A.card := by
    dsimp only [L]
    rw [card_subtype, filter_eq_self.mpr]
    exact fun x hx ↦ mem_union_left _ hx
  have hM : M.card = B.card := by
    dsimp only [M]
    rw [card_subtype, filter_eq_self.mpr]
    exact fun x hx ↦ mem_union_right _ hx
  have hJM : J.IsBipartiteWith (L : Set (S : Set V)) (M : Set (S : Set V)) := by
    constructor
    · rw [Set.disjoint_left]
      intro x hx hy
      exact Set.disjoint_left.mp hAB.disjoint (mem_subtype.mp hx) (mem_subtype.mp hy)
    · intro x y hxy
      rcases hAB.mem_of_adj (show G.Adj x.val y.val from hxy) with h | h
      · exact Or.inl ⟨mem_subtype.mpr h.1, mem_subtype.mpr h.2⟩
      · exact Or.inr ⟨mem_subtype.mpr h.1, mem_subtype.mpr h.2⟩
  have hcover : L ∪ M = univ := by
    ext x
    simp only [mem_union, L, M, mem_subtype, mem_univ, iff_true]
    exact mem_union.mp x.property
  have hsupport : G.support ⊆ (S : Set V) := by
    intro x hx
    obtain ⟨y, hxy⟩ := hx
    exact (hAB.mem_of_adj hxy).elim (fun h ↦ mem_union_left _ h.1)
      (fun h ↦ mem_union_right _ h.1)
  have hJcard : J.edgeFinset.card = G.edgeFinset.card := by
    let φ := Copy.induce G (S : Set V)
    have hsurj : Function.Surjective φ.mapEdgeSet := by
      intro ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | _ a b =>
        have hab : G.Adj a b := he
        have ha := hsupport ⟨b, hab⟩
        have hb := hsupport ⟨a, hab.symm⟩
        exact ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), he⟩, rfl⟩
    rw [edgeFinset_card, edgeFinset_card]
    exact Fintype.card_congr (Equiv.ofBijective φ.mapEdgeSet ⟨φ.mapEdgeSet.injective, hsurj⟩)
  have hham := hamiltonian_of_dense_balanced_bipartite J hJM hcover (hL.trans (hcard.trans hM.symm))
    (by rw [hL, hJcard]; exact hedges)
  have hVcard : Fintype.card (S : Set V) = 2 * A.card :=
    (Fintype.card_of_finset' S (fun _ ↦ Iff.rfl)).trans hS
  obtain ⟨u, p, hp⟩ := hham (by rw [hVcard]; omega)
  let φ : J →g G := ⟨Subtype.val, fun h ↦ h⟩
  refine ⟨u.val, p.map φ, hp.isCycle.map Subtype.val_injective, ?_, ?_⟩
  · rw [Walk.length_map, hp.length_eq, hVcard]
  · intro x
    rw [Walk.support_map]
    constructor
    · intro hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact v.property
    · intro hx
      exact List.mem_map.mpr ⟨⟨x, hx⟩, hp.mem_support _, rfl⟩

end Erdos1105

#print axioms Erdos1105.cycle_of_dense_bipartite_parts
