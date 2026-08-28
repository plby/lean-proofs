import ErdosProblems.Erdos577.Subpartitions
import ErdosProblems.Erdos577.ChainExchange

/-! Assemble triangle chains while retaining the specified block family and scores. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace TriangleChain

lemma exists_of_triangle_with_blocks {s : Finset V} (hs : s.card = 4)
    (p : BlockPartition G (univ \ s)) (ht : TriangleIn G s) :
    ∃ c : TriangleChain G, c.remainder = s ∧ c.blocks = p.blocks := by
  obtain ⟨t, hts, ht⟩ := ht
  have hd : (s \ t).card = 1 := by rw [card_sdiff_of_subset hts, hs, ht.card_eq]
  obtain ⟨x, hx⟩ := card_eq_one.mp hd
  have hxm : x ∈ s \ t := by rw [hx]; exact mem_singleton_self _
  have he : insert x t = s := by
    calc
      insert x t = t ∪ {x} := by ext v; simp
      _ = t ∪ (s \ t) := by rw [hx]
      _ = s := union_sdiff_of_subset hts
  let hp : BlockPartition G (univ \ insert x t) := {
    blocks := p.blocks
    disjoint := p.disjoint
    cover := p.cover.trans (congrArg (fun r ↦ univ \ r) he.symm)
    quad := p.quad }
  exact ⟨ofPartition ht (mem_sdiff.mp hxm).2 hp, he, rfl⟩

variable [DecidableRel G.Adj]

lemma Feasible.partition_score_le {c : TriangleChain G} (hc : c.Feasible)
    {s : Finset V} (hs : s.card = 4) (p : BlockPartition G (univ \ s))
    (ht : TriangleIn G s) : p.weightSum (edgeCount G) ≤ c.edgeScore := by
  obtain ⟨d, _, hd⟩ := exists_of_triangle_with_blocks hs p ht
  have hm := hc.edge_max d
  simpa only [edgeScore, hd, BlockPartition.weightSum] using hm

lemma Feasible.partition_complete_le {c : TriangleChain G} (hc : c.Feasible)
    {s : Finset V} (hs : s.card = 4) (p : BlockPartition G (univ \ s))
    (ht : TriangleIn G s) (hedge : p.weightSum (edgeCount G) = c.edgeScore) :
    p.weightSum (fun b ↦ if edgeCount G b = 6 then 1 else 0) ≤ c.completeScore := by
  obtain ⟨d, _, hd⟩ := exists_of_triangle_with_blocks hs p ht
  have he : d.edgeScore = c.edgeScore := by
    simpa only [edgeScore, hd, BlockPartition.weightSum] using hedge
  have hm := hc.complete_max d he
  simpa only [completeScore_eq_sum, hd, BlockPartition.weightSum] using hm

end TriangleChain

namespace BlockPartition

/-- A factor on the remainder and selected blocks extends to the exact global packing. -/
lemma hasPacking_of_selected_factor {r : Finset V} (p : BlockPartition G (univ \ r))
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (bs : Finset (Finset V)) (hbs : bs ⊆ p.blocks)
    (q : BlockPartition G (r ∪ bs.biUnion id)) : HasPacking G k := by
  have hp := p.splice bs hbs q subset_rfl
  have hs : (univ \ ((r ∪ bs.biUnion id) \ (r ∪ bs.biUnion id)) : Finset V).card = 4 * k := by
    simp [hcard]
  exact hp.hasPacking_of_card k hs

end BlockPartition

end Erdos577
