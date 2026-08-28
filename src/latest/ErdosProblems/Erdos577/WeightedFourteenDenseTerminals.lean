import ErdosProblems.Erdos577.WeightedFourteenDenseRows
import ErdosProblems.Erdos577.HighPairLeafExchange

/-! All four terminals of the forced twelve-vertex core have feasible presentations. -/

namespace Erdos577.WeightedFourteen.Dense

open Finset

variable {V : Type*} {G : SimpleGraph V}

def terminals (p : Paw G) (q v : Quadrilateral G) : Fin 4 → V := ![p.leaf, q 1, q 3, v 1]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem exists_terminal_chain {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (special : Fin 3) (hrows : Rows p q v special) (tag : Fin 4) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = terminals p q v tag ∧
      d.triangle = p.triangle ∧
      ∀ t ∈ c.blocks, t ≠ b → t ≠ a → t ∈ d.blocks := by
  have hold (j : Fin 3) :
      ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = terminal p q j ∧
        d.triangle = p.triangle ∧ ∀ t ∈ c.blocks, t ≠ b → t ≠ a → t ∈ d.blocks := by
    obtain ⟨d, hdF, hdx, hdt, hkeep⟩ :=
      WeightedFourteen.exists_terminal_chain hc p hp hb q hq hd h j
    exact ⟨d, hdF, hdx, hdt, fun t ht htb _ ↦ hkeep t ht htb⟩
  fin_cases tag
  · exact hold 0
  · exact hold 1
  · exact hold 2
  · have hdv : Disjoint p.support v.support := by
      rw [hp, hv]
      apply disjoint_left.mpr
      intro u hu hua
      exact (mem_sdiff.mp (c.complementPartition.block_subset ha hua)).2 hu
    obtain ⟨d, hdF, hdx, hdt, hkeep⟩ := hc.exists_high_pair_leaf_terminal p hp ha v hv hdv
      hrows.1.2 (hrows.leaf p q v special) 1 (Or.inl rfl)
    exact ⟨d, hdF, hdx, hdt, fun t ht _ hta ↦ hkeep t ht hta⟩

theorem terminal_universal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (special : Fin 3) (hrows : Rows p q v special) (tag : Fin 4)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (h3 : 3 ≤ degreeIn G (terminals p q v tag) t) (u : V) (hu : u ∈ t) :
    QuadOn G (insert (terminals p q v tag) (t.erase u)) := by
  obtain ⟨d, hdF, hdx, _, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h ha v hv
    special hrows tag
  rw [← hdx] at h3 ⊢
  exact hdF.terminal_universal_replace (hkeep t ht htb hta) h3 hu

end Erdos577.WeightedFourteen.Dense
