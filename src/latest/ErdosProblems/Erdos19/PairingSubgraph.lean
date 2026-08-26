import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic

/-! # Matchings obtained by pairing two disjoint sets injectively -/

namespace Erdos19

open _root_.SimpleGraph

variable {V T : Type*} (G : _root_.SimpleGraph V) (left right : T → V)
  (hadj : ∀ i, G.Adj (left i) (right i))

def pairingSubgraph : G.Subgraph := ⨆ i, G.subgraphOfAdj (hadj i)

theorem pairingSubgraph_verts :
    (pairingSubgraph G left right hadj).verts = Set.range left ∪ Set.range right := by
  ext v
  simp only [pairingSubgraph, Subgraph.verts_iSup, Set.mem_iUnion, subgraphOfAdj_verts,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨i, h | h⟩
    · exact Or.inl ⟨i, h.symm⟩
    · exact Or.inr ⟨i, h.symm⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl hi.symm⟩
    · exact ⟨i, Or.inr hi.symm⟩

theorem pairingSubgraph_adj (x y : V) :
    (pairingSubgraph G left right hadj).Adj x y ↔
      ∃ i, (left i = x ∧ right i = y) ∨ (left i = y ∧ right i = x) := by
  simp only [pairingSubgraph, Subgraph.iSup_adj, subgraphOfAdj_adj, Sym2.eq_iff]

theorem pairingSubgraph_isMatching
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hdis : Disjoint (Set.range left) (Set.range right)) :
    (pairingSubgraph G left right hadj).IsMatching := by
  apply Subgraph.IsMatching.iSup (fun i ↦ Subgraph.IsMatching.subgraphOfAdj (hadj i))
  intro i j hij
  rw [Subgraph.IsMatching.support_eq_verts (Subgraph.IsMatching.subgraphOfAdj (hadj i)),
    Subgraph.IsMatching.support_eq_verts (Subgraph.IsMatching.subgraphOfAdj (hadj j)),
    subgraphOfAdj_verts, subgraphOfAdj_verts]
  apply Set.disjoint_left.mpr
  rintro v (hvi | hvi) (hvj | hvj)
  · exact hij (hleft (hvi.symm.trans hvj))
  · exact Set.disjoint_left.mp hdis ⟨i, hvi.symm⟩ ⟨j, hvj.symm⟩
  · exact Set.disjoint_left.mp hdis ⟨j, hvj.symm⟩ ⟨i, hvi.symm⟩
  · exact hij (hright (hvi.symm.trans hvj))

#print axioms pairingSubgraph_isMatching

end Erdos19
