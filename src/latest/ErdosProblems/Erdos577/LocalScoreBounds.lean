import ErdosProblems.Erdos577.LocalAssembly

/-! Convert a bounded local edge loss into the two global feasibility bounds. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Feasible.one_edge_loss_bound {c : TriangleChain G} (hc : c.Feasible)
    {r b : Finset V} (p : BlockPartition G (univ \ r)) (hb : b ∈ p.blocks)
    (d : LocalChain G (r ∪ b)) (hloss : edgeCount G b ≤ edgeCount G d.block + 1) :
    p.weightSum (edgeCount G) ≤ c.edgeScore + 1 ∧
      (p.weightSum (edgeCount G) = c.edgeScore + 1 →
        p.weightSum (fun q ↦ if edgeCount G q = 6 then 1 else 0) ≤ c.completeScore + 1) := by
  have he := p.chainOfLocal_edgeScore b hb d
  have hmax := hc.edge_max (p.chainOfLocal b hb d)
  constructor
  · omega
  · intro hp
    have heq : (p.chainOfLocal b hb d).edgeScore = c.edgeScore := by omega
    have hm := hc.complete_max (p.chainOfLocal b hb d) heq
    have ht := p.chainOfLocal_completeScore b hb d
    have hbound : (if edgeCount G b = 6 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    omega

lemma Feasible.min_five_reduction_bound {c : TriangleChain G} (hc : c.Feasible)
    {r b : Finset V} (p : BlockPartition G (univ \ r)) (hb : b ∈ p.blocks)
    (d : LocalChain G (r ∪ b)) (hnew : min (edgeCount G b) 5 ≤ edgeCount G d.block) :
    p.weightSum (edgeCount G) ≤ c.edgeScore + 1 ∧
      (p.weightSum (edgeCount G) = c.edgeScore + 1 →
        p.weightSum (fun q ↦ if edgeCount G q = 6 then 1 else 0) ≤ c.completeScore + 1) := by
  have hb6 := (p.quad b hb).edgeCount_le_six
  have hloss : edgeCount G b ≤ edgeCount G d.block + 1 := by
    rcases le_total (edgeCount G b) 5 with h | h
    · rw [min_eq_left h] at hnew
      omega
    · rw [min_eq_right h] at hnew
      omega
  exact hc.one_edge_loss_bound p hb d hloss

end Erdos577.TriangleChain
