import ErdosProblems.Erdos19.Core

/-! # Elementary size bounds for nonadjacent neighbor pairs -/

namespace Erdos19

theorem nonadjacentNeighborPairs_ncard_le_sq {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (v : V) :
    (nonadjacentNeighborPairGraph G v).edgeSet.ncard ≤ (G.neighborSet v).ncard ^ 2 := by
  classical
  let code (e : (nonadjacentNeighborPairGraph G v).edgeSet) :
      G.neighborSet v × G.neighborSet v :=
    (⟨e.1.out.1, (nonadjacentNeighborPairGraph_edge_out G v e).2.1⟩,
      ⟨e.1.out.2, (nonadjacentNeighborPairGraph_edge_out G v e).2.2.1⟩)
  have hinj : Function.Injective code := by
    intro e f h
    have h₁ : e.1.out.1 = f.1.out.1 := congrArg (fun p ↦ p.1.1) h
    have h₂ : e.1.out.2 = f.1.out.2 := congrArg (fun p ↦ p.2.1) h
    apply Subtype.ext
    rw [← sym2_mk_out_eq e.1, ← sym2_mk_out_eq f.1, h₁, h₂]
  have h := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_prod, Set.fintypeCard_eq_ncard, pow_two] using h

theorem two_le_neighbor_ncard_of_nonadjacentPair {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (v : V)
    (hpos : 0 < (nonadjacentNeighborPairGraph G v).edgeSet.ncard) :
    2 ≤ (G.neighborSet v).ncard := by
  obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hpos)
  have hpair := nonadjacentNeighborPairGraph_edge_out G v ⟨e, he⟩
  have hsub : ({e.out.1, e.out.2} : Set V) ⊆ G.neighborSet v := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hpair.2.1
    · exact hpair.2.2.1
  simpa only [Set.ncard_pair hpair.1] using Set.ncard_le_ncard hsub

#print axioms nonadjacentNeighborPairs_ncard_le_sq

end Erdos19
