import ErdosProblems.Erdos577.TriangleAssembly

/-! Replace an arbitrary four-vertex remainder and one block by a local triangle chain. -/

namespace Erdos577.BlockPartition

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {r b : Finset V}

lemma local_chain_disjoint (p : BlockPartition G (univ \ r)) (d : LocalChain G (r ∪ b)) :
    Disjoint ((univ \ r) \ b) d.block := by
  have hsub : d.block ⊆ r ∪ ({b} : Finset (Finset V)).biUnion id := by
    simpa only [singleton_biUnion, id_eq] using d.block_subset
  simpa only [singleton_biUnion, id_eq] using p.splice_disjoint hsub

lemma local_chain_cover (_p : BlockPartition G (univ \ r)) (d : LocalChain G (r ∪ b)) :
    ((univ \ r) \ b) ∪ d.block = univ \ d.remainder := by
  ext v
  have hc : (v ∈ d.remainder ∨ v ∈ d.block) ↔ (v ∈ r ∨ v ∈ b) := by
    rw [← mem_union, ← mem_union]
    exact congrArg (fun s ↦ v ∈ s) d.cover |>.to_iff
  have hd : ¬(v ∈ d.remainder ∧ v ∈ d.block) :=
    fun h ↦ (disjoint_left.mp d.disjoint) h.1 h.2
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  tauto

def chainOfLocal (p : BlockPartition G (univ \ r)) (b : Finset V) (hb : b ∈ p.blocks)
    (d : LocalChain G (r ∪ b)) : TriangleChain G :=
  TriangleChain.ofPartition d.triangle_clique d.terminal_not_mem {
    blocks := p.blocks.erase b ∪ {d.block}
    disjoint := ((p.remove b hb).union (single d.quad) (p.local_chain_disjoint d)).disjoint
    cover := by
      have h := ((p.remove b hb).union (single d.quad) (p.local_chain_disjoint d)).cover
      exact h.trans (p.local_chain_cover d)
    quad := ((p.remove b hb).union (single d.quad) (p.local_chain_disjoint d)).quad }

@[simp] lemma chainOfLocal_terminal (p : BlockPartition G (univ \ r)) (b : Finset V)
    (hb : b ∈ p.blocks) (d : LocalChain G (r ∪ b)) :
    (p.chainOfLocal b hb d).terminal = d.terminal := rfl

@[simp] lemma chainOfLocal_triangle (p : BlockPartition G (univ \ r)) (b : Finset V)
    (hb : b ∈ p.blocks) (d : LocalChain G (r ∪ b)) :
    (p.chainOfLocal b hb d).triangle = d.triangle := rfl

@[simp] lemma chainOfLocal_blocks (p : BlockPartition G (univ \ r)) (b : Finset V)
    (hb : b ∈ p.blocks) (d : LocalChain G (r ∪ b)) :
    (p.chainOfLocal b hb d).blocks = p.blocks.erase b ∪ {d.block} := rfl

variable [DecidableRel G.Adj]

lemma chainOfLocal_edgeScore (p : BlockPartition G (univ \ r)) (b : Finset V)
    (hb : b ∈ p.blocks) (d : LocalChain G (r ∪ b)) :
    (p.chainOfLocal b hb d).edgeScore + edgeCount G b =
      p.weightSum (edgeCount G) + edgeCount G d.block :=
  p.weightSum_replace_add b hb d.quad (p.local_chain_disjoint d) (edgeCount G)

lemma chainOfLocal_completeScore (p : BlockPartition G (univ \ r)) (b : Finset V)
    (hb : b ∈ p.blocks) (d : LocalChain G (r ∪ b)) :
    (p.chainOfLocal b hb d).completeScore + (if edgeCount G b = 6 then 1 else 0) =
      p.weightSum (fun q ↦ if edgeCount G q = 6 then 1 else 0) +
        (if edgeCount G d.block = 6 then 1 else 0) := by
  rw [TriangleChain.completeScore_eq_sum]
  exact p.weightSum_replace_add b hb d.quad (p.local_chain_disjoint d)
    (fun q ↦ if edgeCount G q = 6 then 1 else 0)

end Erdos577.BlockPartition
