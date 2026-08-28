import ErdosProblems.Erdos577.PathExchange

/-! The auxiliary attachment maximum, retained only while proving strong-chain existence. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace TriangleChain

lemma covered_eq_complement (c : TriangleChain G) : c.covered = univ \ c.remainder := by
  ext v
  simp only [mem_sdiff, mem_univ, true_and]
  constructor
  · intro hv hr
    exact (disjoint_left.mp c.property.remainder_disjoint) hr hv
  · intro hv
    have hm : v ∈ c.remainder ∪ c.covered := by rw [c.property.cover]; exact mem_univ _
    exact (mem_union.mp hm).resolve_left hv

def complementPartition (c : TriangleChain G) : BlockPartition G (univ \ c.remainder) where
  blocks := c.blocks
  disjoint := c.property.blocks_disjoint
  cover := c.covered_eq_complement
  quad := c.property.blocks_quad

variable [DecidableRel G.Adj]

def attachmentScore (c : TriangleChain G) : ℕ := degreeIn G c.terminal c.triangle

/-- The third score is an auxiliary existence device, not a premise imposed
on every later feasible chain. -/
structure Refined (c : TriangleChain G) : Prop extends c.Feasible where
  attachment_max : ∀ d : TriangleChain G, d.edgeScore = c.edgeScore →
    d.completeScore = c.completeScore → d.attachmentScore ≤ c.attachmentScore

theorem exists_refined (hn : Nonempty (TriangleChain G)) : ∃ c : TriangleChain G, c.Refined := by
  classical
  obtain ⟨c, hc⟩ := exists_feasible hn
  let firstTwo : Finset (TriangleChain G) :=
    univ.filter fun d ↦ d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore
  have hm : firstTwo.Nonempty := ⟨c, by simp [firstTwo]⟩
  obtain ⟨d, hd, hmax⟩ := firstTwo.exists_max_image attachmentScore hm
  have hed := (mem_filter.mp hd).2.1
  have hcd := (mem_filter.mp hd).2.2
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · intro e
    rw [hed]
    exact hc.edge_max e
  · intro e he
    rw [hcd]
    exact hc.complete_max e (he.trans hed)
  · intro e he hc'
    apply hmax e
    exact mem_filter.mpr ⟨mem_univ _, he.trans hed, hc'.trans hcd⟩

end TriangleChain

theorem Saturated.exists_refined_chain [DecidableRel G.Adj] {k : ℕ} (h : Saturated G k)
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) :
    ∃ c : TriangleChain G, c.Refined :=
  TriangleChain.exists_refined (h.exists_triangle_chain hcard hdeg)

end Erdos577
