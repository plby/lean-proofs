import ErdosProblems.Erdos577.JointBridgeRows

/-! General strong terminals with the original center and an unchanged ordered triangle. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def centerPaw (p : Paw G) (u : V) (hu : u ∉ p.support)
    (hru : G.Adj p.center u) : Paw G :=
  Paw.ofVertices u p.center (p.vertices 2) (p.vertices 3)
    (fun he ↦ hu (he.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩))
    (fun he ↦ hu (he.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩))
    (fun he ↦ hu (he.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩))
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3))
    (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 3))
    hru.symm p.edge12 p.edge13 p.edge23

lemma centerPaw_triangle (p : Paw G) (u : V) (hu : u ∉ p.support)
    (hru : G.Adj p.center u) : (centerPaw p u hu hru).triangle = p.triangle := rfl

lemma centerPaw_support (p : Paw G) (u : V) (hu : u ∉ p.support)
    (hru : G.Adj p.center u) :
    (centerPaw p u hu hru).support = insert u p.triangle := (centerPaw p u hu hru).support_eq

variable [Fintype V] [DecidableRel G.Adj]

theorem strong_of_center_neighbor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hT : c.triangle = p.triangle) (hr : G.Adj p.center c.terminal) : c.Strong := by
  have hbound := c.terminal_degree_le_one hcard hn
  rw [hT] at hbound
  have hpos : 0 < degreeIn G c.terminal p.triangle := card_pos.mpr
    ⟨p.center, mem_filter.mpr ⟨p.center_mem_triangle, hr.symm⟩⟩
  refine ⟨hc, ?_⟩
  change degreeIn G c.terminal c.triangle = 1
  rw [hT]
  omega

theorem full_row_exposes_neighbor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hT : c.triangle = p.triangle)
    {b : Finset V} (hb : b ∈ c.blocks) (hfull : degreeIn G c.terminal b = 4)
    (u : V) (hu : u ∈ b) (hru : G.Adj p.center u) :
    ∃ d : TriangleChain G, d.Strong ∧ d.terminal = u ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase b ∪ {insert c.terminal (b.erase u)} := by
  have hcl := hc.clique_of_terminal_degree_four hb hfull
  have hquad := hc.terminal_universal_replace hb (by omega) hu
  have hxu := (degreeIn_eq_card_iff c.terminal b).mp (hfull.trans hcl.card_eq.symm) u hu
  have hrow := degreeIn_erase_add G c.terminal u hu
  rw [hfull, if_pos hxu] at hrow
  have hdu := degreeIn_clique G hcl.isClique hu
  rw [hcl.card_eq] at hdu
  have hscore := edgeCount_replace G u c.terminal hu (c.terminal_not_mem_block hb)
  obtain ⟨d, hd, ht, hT', he, hcomp, hblocks⟩ := hc.exists_terminal_swap hb hu hquad (by omega)
  have htri := hT'.trans hT
  exact ⟨d, strong_of_center_neighbor hd hcard hn p htri (ht.symm ▸ hru),
    ht, htri, he, hcomp, hblocks⟩

theorem missed_row_exposes_neighbor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hT : c.triangle = p.triangle)
    {b : Finset V} (hb : b ∈ c.blocks) (hthree : degreeIn G c.terminal b = 3)
    (u : V) (hu : u ∈ b) (hmiss : ¬G.Adj c.terminal u) (hru : G.Adj p.center u) :
    ∃ d : TriangleChain G, d.Strong ∧ d.terminal = u ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase b ∪ {insert c.terminal (b.erase u)} := by
  have hrow := degreeIn_erase_add G c.terminal u hu
  rw [hthree, if_neg hmiss] at hrow
  have hrow3 : degreeIn G c.terminal (b.erase u) = 3 := by omega
  have hdu := hc.terminal_replacement_degree hb hu hrow3
  have hquad := hc.terminal_universal_replace hb (by omega) hu
  have hscore := edgeCount_replace G u c.terminal hu (c.terminal_not_mem_block hb)
  obtain ⟨d, hd, ht, hT', he, hcomp, hblocks⟩ := hc.exists_terminal_swap hb hu hquad (by omega)
  have htri := hT'.trans hT
  exact ⟨d, strong_of_center_neighbor hd hcard hn p htri (ht.symm ▸ hru),
    ht, htri, he, hcomp, hblocks⟩

end Erdos577.JointBridge
