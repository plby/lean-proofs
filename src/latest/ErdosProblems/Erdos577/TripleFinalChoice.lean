import ErdosProblems.Erdos577.ThreeRowsChoice

/-! The first complete heavy block and a chosen common neighbor for Claim2.7. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure HeavyChoice (c : TriangleChain G) (p : Paw G) (q : Quadrilateral G)
    (a : Finset V) (u : V) : Prop extends Configuration c p q where
  heavy_mem : a ∈ c.blocks
  heavy_ne : a ≠ q.support
  heavy_complete : G.IsNClique 4 a
  second_zero : degreeIn G (p.vertices 2) a = 0
  third_zero : degreeIn G (p.vertices 3) a = 0
  three_rows : 11 ≤ degreeIn G p.leaf a + degreeIn G p.center a + degreeIn G (q 3) a
  chosen_mem : u ∈ a
  leaf_chosen : G.Adj p.leaf u
  center_chosen : G.Adj p.center u
  replacement_complete : G.IsNClique 4 (insert (q 3) (a.erase u))

theorem Configuration.exists_heavy_choice {c : TriangleChain G} {p : Paw G}
    {q : Quadrilateral G} (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) : ∃ a u, HeavyChoice c p q a u := by
  obtain ⟨a, ha, haq, hheavy⟩ := h.exists_heavy_block hcard hdeg hn
  obtain ⟨hcl, hb, ht, hrows⟩ := h.heavy_block hc hcard hdeg hn ha haq hheavy
  obtain ⟨u, hu, hxu, hru, hrep⟩ :=
    three_rows_choose_complete_replacement hcl p.leaf p.center (q 3) hrows
  exact ⟨a, u, h, ha, haq, hcl, hb, ht, hrows, hu, hxu, hru, hrep⟩

end Erdos577.UniversalTriple
