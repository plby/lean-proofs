import ErdosProblems.Erdos577.TripleHeavyColumns

/-! A triangle with a no-sparser complementary block gives an actual equal-score strong chain. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.exchange_core_triangle {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {a : Finset V} (ha : a ∈ c.blocks) (p : Paw G) (hleaf : p.leaf = c.terminal)
    (hsub : p.triangle ⊆ c.triangle ∪ a)
    (hquad : QuadOn G ((c.triangle ∪ a) \ p.triangle))
    (hscore : edgeCount G a ≤ edgeCount G ((c.triangle ∪ a) \ p.triangle)) :
    ∃ d : TriangleChain G, d.Strong ∧ p.support = d.remainder ∧
      d.terminal = p.leaf ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase a ∪ {(c.triangle ∪ a) \ p.triangle} := by
  have hx : c.terminal ∉ c.triangle ∪ a := by
    rw [mem_union, not_or]
    exact ⟨c.property.terminal_not_mem, c.terminal_not_mem_block ha⟩
  let b := (c.triangle ∪ a) \ p.triangle
  let loc : LocalChain G (c.remainder ∪ a) := {
    terminal := p.leaf
    triangle := p.triangle
    block := b
    triangle_clique := p.triangle_clique
    terminal_not_mem := p.leaf_not_mem_triangle
    quad := hquad
    disjoint := disjoint_insert_left.mpr ⟨by
      rw [hleaf]
      exact fun hh ↦ hx (mem_sdiff.mp hh).1, disjoint_sdiff_self_right⟩
    cover := by
      rw [insert_union, union_sdiff_of_subset hsub, hleaf]
      change insert c.terminal (c.triangle ∪ a) = insert c.terminal c.triangle ∪ a
      rw [insert_union] }
  have hle := hc.local_edges_le ha loc
  have he : edgeCount G loc.block = edgeCount G a := Nat.le_antisymm hle hscore
  let d := c.replaceBlock a ha loc
  have hd : d.Feasible := hc.replaceBlock_feasible ha loc he
  have hstrong : d.Strong := by
    refine ⟨hd, ?_⟩
    change degreeIn G p.leaf p.triangle = 1
    exact p.leaf_triangle_degree_eq_one (by
      rw [p.support_eq]
      exact d.no_quad_remainder hcard hn)
  have hscores := c.replaceBlock_scores_eq ha loc he
  exact ⟨d, hstrong, p.support_eq, rfl, rfl, hscores.1, hscores.2, rfl⟩

end Erdos577
