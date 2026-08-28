import ErdosProblems.Erdos577.Replacements
import ErdosProblems.Erdos577.ChainExchange
import ErdosProblems.Erdos577.QuadDegrees

/-! Feasibility forces the diagonals needed for every high-degree terminal replacement. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma QuadOn.replace_of_complete_erase {s : Finset V} (hs : QuadOn G s)
    {z u : V} (hz : z ∉ s) (hu : u ∈ s) (hrow : ∀ w ∈ s.erase u, G.Adj z w) :
    QuadOn G (insert z (s.erase u)) := by
  obtain ⟨q, rfl⟩ := hs
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
  apply q.quad_replaceAt i z hz
  intro j hij
  apply hrow
  exact mem_erase.mpr ⟨fun h ↦ hij.ne (q.injective h).symm,
    (q.mem_support _).mpr ⟨j, rfl⟩⟩

lemma QuadOn.replace_of_three_after_erase {s : Finset V} (hs : QuadOn G s)
    {z u : V} (hz : z ∉ s) (hu : u ∈ s) (hrow : degreeIn G z (s.erase u) = 3) :
    QuadOn G (insert z (s.erase u)) := by
  have hcard : (s.erase u).card = 3 := by rw [card_erase_of_mem hu, hs.card]
  exact hs.replace_of_complete_erase hz hu
    ((degreeIn_eq_card_iff z (s.erase u)).mp (hrow.trans hcard.symm))

/-- A row of at least three contacts permits every replacement when each
nonneighbor has all three possible internal neighbors. -/
lemma QuadOn.universal_replace_of_nonadjacent_degree {s : Finset V} (hs : QuadOn G s)
    {z : V} (hz : z ∉ s) (hrow : 3 ≤ degreeIn G z s)
    (hhigh : ∀ u ∈ s, ¬G.Adj z u → 3 ≤ degreeIn G u s)
    {v : V} (hv : v ∈ s) : QuadOn G (insert z (s.erase v)) := by
  have hze : z ∉ s.erase v := fun h ↦ hz (mem_erase.mp h).2
  apply QuadOn.of_degreeIn
  · rw [card_insert_of_notMem hze, card_erase_of_mem hv, hs.card]
  · intro w hw
    rcases mem_insert.mp hw with hw | hw
    · subst w
      have he := degreeIn_erase_add G z v hv
      rw [degreeIn_insert G z z hze]
      simp only [SimpleGraph.irrefl, if_false, Nat.zero_add]
      split_ifs at he <;> omega
    · obtain ⟨_, hws⟩ := mem_erase.mp hw
      have he := degreeIn_erase_add G w v hv
      have htwo := hs.two_le_degreeIn hws
      rw [degreeIn_insert G w z hze]
      by_cases hwz : G.Adj w z
      · rw [if_pos hwz]
        split_ifs at he <;> omega
      · rw [if_neg hwz]
        have hthree := hhigh w hws (fun h ↦ hwz h.symm)
        split_ifs at he <;> omega

namespace TriangleChain

variable [Fintype V]

omit [DecidableRel G.Adj] in
lemma terminal_not_mem_block (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks) :
    c.terminal ∉ b := by
  intro hx
  exact (mem_sdiff.mp (c.complementPartition.block_subset hb hx)).2 (mem_insert_self _ _)

def swapTerminal (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks)
    {u : V} (hu : u ∈ b) (hq : QuadOn G (insert c.terminal (b.erase u))) :
    LocalChain G (c.remainder ∪ b) where
  terminal := u
  triangle := c.triangle
  block := insert c.terminal (b.erase u)
  triangle_clique := c.property.triangle_clique
  terminal_not_mem := by
    intro ht
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hu)).2
      (mem_insert_of_mem ht)
  quad := hq
  disjoint := by
    apply disjoint_left.mpr
    intro w hw hnew
    rcases mem_insert.mp hnew with rfl | hnew
    · rcases mem_insert.mp hw with h | h
      · exact c.terminal_not_mem_block hb (h ▸ hu)
      · exact c.property.terminal_not_mem h
    · rcases mem_insert.mp hw with rfl | hw
      · exact (mem_erase.mp hnew).1 rfl
      · exact (mem_sdiff.mp (c.complementPartition.block_subset hb
          (mem_erase.mp hnew).2)).2 (mem_insert_of_mem hw)
  cover := by
    ext w
    change (w ∈ insert u c.triangle ∪ insert c.terminal (b.erase u)) ↔
      w ∈ insert c.terminal c.triangle ∪ b
    have h : w = u → w ∈ b := fun h ↦ h ▸ hu
    simp only [mem_union, mem_insert, mem_erase]
    tauto

lemma Feasible.terminal_replacement_degree {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) {u : V} (hu : u ∈ b)
    (hrow : degreeIn G c.terminal (b.erase u) = 3) : degreeIn G u b = 3 := by
  have hx := c.terminal_not_mem_block hb
  have hq := (c.property.blocks_quad b hb).replace_of_three_after_erase hx hu hrow
  have hmax := hc.local_edges_le hb (c.swapTerminal hb hu hq)
  change edgeCount G (insert c.terminal (b.erase u)) ≤ edgeCount G b at hmax
  have he := edgeCount_replace G u c.terminal hu hx
  rw [hrow] at he
  have hupper := degreeIn_le_card G u (b.erase u)
  rw [degreeIn_erase_self G u hu, card_erase_of_mem hu,
    (c.property.blocks_quad b hb).card] at hupper
  omega

lemma Feasible.terminal_universal_replace {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (hrow : 3 ≤ degreeIn G c.terminal b)
    {u : V} (hu : u ∈ b) : QuadOn G (insert c.terminal (b.erase u)) := by
  apply (c.property.blocks_quad b hb).universal_replace_of_nonadjacent_degree
    (c.terminal_not_mem_block hb) hrow (fun v hv hnon ↦ ?_) hu
  have he := degreeIn_erase_add G c.terminal v hv
  rw [if_neg hnon] at he
  have hupper := degreeIn_le_card G c.terminal (b.erase v)
  rw [card_erase_of_mem hv, (c.property.blocks_quad b hb).card] at hupper
  have hthree : degreeIn G c.terminal (b.erase v) = 3 := by omega
  exact le_of_eq (hc.terminal_replacement_degree hb hv hthree).symm

lemma Feasible.terminal_replacement_diagonal {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (i : Fin 4) (hrow : degreeIn G c.terminal (b.erase (q i)) = 3) :
    G.Adj (q i) (q (i + 2)) := by
  have hi : q i ∈ b := hq ▸ (q.mem_support _).mpr ⟨i, rfl⟩
  have hdeg := hc.terminal_replacement_degree hb hi hrow
  rw [← hq, q.degreeIn_eq] at hdeg
  by_contra h
  rw [if_neg h] at hdeg
  omega

lemma Feasible.clique_of_terminal_degree_four {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (hrow : degreeIn G c.terminal b = 4) :
    G.IsNClique 4 b := by
  have hcard := (c.property.blocks_quad b hb).card
  have hall := (degreeIn_eq_card_iff c.terminal b).mp (hrow.trans hcard.symm)
  refine ⟨?_, hcard⟩
  intro u hu v hv huv
  have he := degreeIn_erase_add G c.terminal u hu
  rw [if_pos (hall u hu), hrow] at he
  have hthree := hc.terminal_replacement_degree hb hu (by omega)
  have herase : degreeIn G u (b.erase u) = (b.erase u).card := by
    rw [degreeIn_erase_self G u hu, hthree, card_erase_of_mem hu, hcard]
  exact (degreeIn_eq_card_iff u (b.erase u)).mp herase v
    (mem_erase.mpr ⟨Ne.symm huv, hv⟩)

end TriangleChain

end Erdos577
