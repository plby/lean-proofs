import ErdosProblems.Erdos577.ScoredExchange
import ErdosProblems.Erdos577.TerminalReplacements
import ErdosProblems.Erdos577.LocalChainSupport
import ErdosProblems.Erdos577.CliqueCounts

/-! A complete triangle column in a noncomplete block must meet any two-contact terminal. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Feasible.no_triangle_after_high {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hfull : ∀ u ∈ c.triangle, G.Adj (q 0) u) (hscore : edgeCount G b ≤ 5) :
    ¬TriangleIn G (insert c.terminal (q.support.erase (q 0))) := by
  intro ht
  have hd : Disjoint c.remainder q.support := by
    rw [hq]
    apply disjoint_left.mpr
    intro u hu hub
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hub)).2 hu
  have hxq : c.terminal ∉ q.support := by rw [hq]; exact c.terminal_not_mem_block hb
  have htq (u : V) (hu : u ∈ c.triangle) : u ∉ q.support := fun hh ↦
    disjoint_left.mp hd (mem_insert_of_mem hu) hh
  have hqx : c.terminal ≠ q 0 := fun he ↦ hxq (he ▸ (q.mem_support _).mpr ⟨0, rfl⟩)
  have hrem : (c.remainder ∪ q.support) \ insert (q 0) c.triangle =
      insert c.terminal (q.support.erase (q 0)) := by
    ext u
    have h₁ : u ∈ c.triangle → u ∉ q.support := htq u
    have h₂ : u = c.terminal → u ∉ c.triangle := fun he ↦ he ▸ c.property.terminal_not_mem
    have h₃ : u = c.terminal → u ≠ q 0 := fun he ↦ he ▸ hqx
    change u ∈ (insert c.terminal c.triangle ∪ q.support) \ insert (q 0) c.triangle ↔ _
    simp only [mem_sdiff, mem_union, mem_insert, mem_erase]
    tauto
  have hcl : G.IsNClique 4 (insert (q 0) c.triangle) := c.property.triangle_clique.insert hfull
  have hquad : QuadOn G (insert (q 0) c.triangle) := by
    apply QuadOn.of_degreeIn hcl.card_eq
    intro u hu
    rw [degreeIn_clique G hcl.isClique hu, hcl.card_eq]
    decide
  have hsub : insert (q 0) c.triangle ⊆ c.remainder ∪ q.support := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact mem_union_right _ ((q.mem_support _).mpr ⟨0, rfl⟩)
    · exact mem_union_left _ (mem_insert_of_mem hu)
  have hs : (c.remainder ∪ q.support).card = 8 := by
    rw [card_union_of_disjoint hd, c.card_remainder, q.card_support]
  obtain ⟨d, hdblock⟩ := LocalChain.exists_with_block hs hsub hquad (hrem ▸ ht)
  let d' := d.withSupport (show c.remainder ∪ q.support = c.remainder ∪ b by rw [hq])
  have he := hc.local_edges_le hb d'
  change edgeCount G d.block ≤ edgeCount G b at he
  rw [hdblock, edgeCount_clique hcl.isClique, hcl.card_eq] at he
  change 6 ≤ edgeCount G b at he
  omega

lemma Feasible.high_opposite_odd_false {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hfull : ∀ u ∈ c.triangle, G.Adj (q 0) u) (hscore : edgeCount G b ≤ 5)
    (h2 : G.Adj c.terminal (q 2)) (i : Fin 4) (hi : i = 1 ∨ i = 3)
    (hei : G.Adj c.terminal (q i)) : False := by
  apply hc.no_triangle_after_high hb q hq hfull hscore
  have h20 : q 2 ≠ q 0 := fun he ↦ (by decide : (2 : Fin 4) ≠ 0) (q.injective he)
  have hi0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
  have he2i : G.Adj (q 2) (q i) := by
    rcases hi with rfl | rfl
    · exact (q.adjacent 1).symm
    · exact q.adjacent 2
  refine ⟨{c.terminal, q 2, q i}, ?_, SimpleGraph.is3Clique_triple_iff.mpr ⟨h2, hei, he2i⟩⟩
  intro u hu
  rcases mem_insert.mp hu with rfl | hu
  · exact mem_insert_self _ _
  rcases mem_insert.mp hu with rfl | hu
  · exact mem_insert_of_mem (mem_erase.mpr ⟨h20, (q.mem_support _).mpr ⟨2, rfl⟩⟩)
  rw [mem_singleton] at hu
  subst u
  exact mem_insert_of_mem (mem_erase.mpr
    ⟨fun he ↦ hi0 (q.injective he), (q.mem_support _).mpr ⟨i, rfl⟩⟩)

theorem Feasible.terminal_high_contact {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hfull : ∀ u ∈ c.triangle, G.Adj (q 0) u) (hscore : edgeCount G b ≤ 5)
    (hrow : degreeIn G c.terminal q.support = 2) : G.Adj c.terminal (q 0) := by
  by_contra hnon
  have hxq : c.terminal ∉ q.support := by rw [hq]; exact c.terminal_not_mem_block hb
  have hnotboth : ¬(G.Adj c.terminal (q 1) ∧ G.Adj c.terminal (q 3)) := by
    intro hh
    have hrep := q.quad_replaceAt 0 c.terminal hxq (fun j hj ↦ by
      have hidx : ∀ j : Fin 4, (SimpleGraph.cycleGraph 4).Adj 0 j → j = 1 ∨ j = 3 := by
        decide +kernel
      rcases hidx j hj with rfl | rfl
      · exact hh.1
      · exact hh.2)
    rw [hq] at hrep
    have hu : q 0 ∈ b := hq ▸ (q.mem_support _).mpr ⟨0, rfl⟩
    have hl := (c.replaceBlock b hb (c.swapTerminal hb hu hrep)).terminal_degree_le_one hcard hn
    change degreeIn G (q 0) c.triangle ≤ 1 at hl
    have he := (degreeIn_eq_card_iff (q 0) c.triangle).mpr hfull
    rw [c.property.triangle_clique.card_eq] at he
    omega
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have he := degreeIn_image G c.terminal univ q hinj
  change degreeIn G c.terminal q.support = _ at he
  rw [hrow, Fin.sum_univ_four, if_neg hnon] at he
  by_cases h1 : G.Adj c.terminal (q 1)
  · have h3 : ¬G.Adj c.terminal (q 3) := fun hh ↦ hnotboth ⟨h1, hh⟩
    have h2 : G.Adj c.terminal (q 2) := by
      by_contra hh
      rw [if_pos h1, if_neg h3, if_neg hh] at he
      omega
    exact hc.high_opposite_odd_false hb q hq hfull hscore h2 1 (Or.inl rfl) h1
  · have h3 : G.Adj c.terminal (q 3) := by
      by_contra hh
      rw [if_neg h1, if_neg hh] at he
      split_ifs at he <;> omega
    have h2 : G.Adj c.terminal (q 2) := by
      by_contra hh
      rw [if_neg h1, if_pos h3, if_neg hh] at he
      omega
    exact hc.high_opposite_odd_false hb q hq hfull hscore h2 3 (Or.inr rfl) h3

end Erdos577.TriangleChain
