import ErdosProblems.Erdos556.Basic

/-!
# Retaining the edges inside disjoint vertex pieces

This graph construction is used to turn a decomposition into a graph with
controlled edge deletion. For disjoint pieces, its edge count is exactly
the sum of the induced edge counts.
-/

namespace Erdos556

open SimpleGraph Finset

def pieceGraph {V : Type*} (G : SimpleGraph V) (P : Finset (Finset V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∃ A ∈ P, u ∈ A ∧ v ∈ A
  symm := ⟨by
    rintro u v ⟨huv, A, hA, hu, hv⟩
    exact ⟨huv.symm, A, hA, hv, hu⟩⟩
  loopless := ⟨by intro u h; exact h.1.ne rfl⟩

theorem pieceGraph_le {V : Type*} (G : SimpleGraph V) (P : Finset (Finset V)) :
    pieceGraph G P ≤ G := fun _ _ h => h.1

theorem pieceGraph_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V))
    [DecidableRel (pieceGraph G P).Adj]
    (hP : (P : Set (Finset V)).Pairwise Disjoint) :
    (pieceGraph G P).edgeFinset.card = ∑ A ∈ P, (G.induce (A : Set V)).edgeFinset.card := by
  classical
  let E (A : Finset V) := G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  have hedges : (pieceGraph G P).edgeFinset = P.biUnion E := by
    ext e
    rcases e with ⟨⟨u, v⟩⟩
    change s(u, v) ∈ (pieceGraph G P).edgeFinset ↔ s(u, v) ∈ P.biUnion E
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change (G.Adj u v ∧ ∃ A ∈ P, u ∈ A ∧ v ∈ A) ↔ s(u, v) ∈ P.biUnion E
    simp only [mem_edgeFinset, mem_edgeSet, mem_biUnion, E, mem_filter,
      Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
    constructor
    · rintro ⟨huv, A, hA, hu, hv⟩
      exact ⟨A, hA, huv, hu, hv⟩
    · rintro ⟨A, hA, huv, hu, hv⟩
      exact ⟨huv, A, hA, hu, hv⟩
  have hdisj : (P : Set (Finset V)).Pairwise fun A B => Disjoint (E A) (E B) := by
    intro A hA B hB hAB
    rw [Finset.disjoint_left]
    intro e heA heB
    have ha := (mem_filter.mp heA).2
    have hb := (mem_filter.mp heB).2
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
    exact Finset.disjoint_left.mp (hP hA hB hAB) (ha hv) (hb hv)
  rw [hedges, card_biUnion hdisj]
  apply sum_congr rfl
  intro A _
  exact G.card_filter_edgeFinset_toFinset_subset A

#print axioms pieceGraph_card_edges

theorem pieceGraph_colorable {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) (n : ℕ) [NeZero n]
    (hP : (P : Set (Finset V)).Pairwise Disjoint)
    (hcolour : ∀ A ∈ P, (G.induce (A : Set V)).Colorable n) :
    (pieceGraph G P).Colorable n := by
  classical
  let C (A : P) : (G.induce (A.val : Set V)).Coloring (Fin n) :=
    Classical.choice (hcolour A.val A.property)
  let Q (v : V) : Prop := ∃ A : P, v ∈ A.val
  let f (v : V) : Fin n := if h : Q v then
    C (Classical.choose h) ⟨v, Classical.choose_spec h⟩ else 0
  have hf (A : P) (v : V) (hv : v ∈ A.val) : f v = C A ⟨v, hv⟩ := by
    have hvQ : Q v := ⟨A, hv⟩
    dsimp [f]
    rw [dif_pos hvQ]
    have heq : Classical.choose hvQ = A := by
      apply Subtype.ext
      by_contra hne
      exact Finset.disjoint_left.mp
        (hP (Classical.choose hvQ).property A.property hne) (Classical.choose_spec hvQ) hv
    subst heq
    rfl
  refine ⟨{ toFun := f, map_rel' := ?_ }⟩
  intro u v huv
  obtain ⟨hG, A, hA, hu, hv⟩ := huv
  rw [hf ⟨A, hA⟩ u hu, hf ⟨A, hA⟩ v hv]
  exact (C ⟨A, hA⟩).valid hG

#print axioms pieceGraph_colorable

end Erdos556
