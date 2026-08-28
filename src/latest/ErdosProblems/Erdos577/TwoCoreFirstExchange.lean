import ErdosProblems.Erdos577.FullRowCompleteBlock
import ErdosProblems.Erdos577.GlobalPathTransfer
import ErdosProblems.Erdos577.CoreCliqueFactorSupport

/-! The first equal-score terminal exposure and unique core neighbor for Wang4.11. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma erase_one_support (q : Quadrilateral G) :
    q.support.erase (q 1) = {q 0, q 2, q 3} := by
  have h01 : q 0 ≠ q 1 := q.injective.ne (by decide : (0 : Fin 4) ≠ 1)
  have h1 : q 1 ∉ ({q 2, q 3} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨q.injective.ne (by decide : (1 : Fin 4) ≠ 2),
      q.injective.ne (by decide : (1 : Fin 4) ≠ 3)⟩
  rw [q.support_four, erase_insert_of_ne h01, erase_insert h1]

lemma leaf_replacement (q : Quadrilateral G) (x : V) (hx : x ∉ q.support)
    (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj x (q i) ↔ (9 : ℕ).testBit i.val = true) :
    QuadOn G (insert x (q.support.erase (q 1))) ∧
      edgeCount G (insert x (q.support.erase (q 1))) = edgeCount G q.support := by
  have h0 : G.Adj x (q 0) := (hrow 0).mpr (by decide)
  have h3 : G.Adj x (q 3) := (hrow 3).mpr (by decide)
  have hn1 : ¬G.Adj x (q 1) := fun hh ↦ by have hh' := (hrow 1).mp hh; contradiction
  have hquad := QuadOn.of_vertices (G := G) (a := x) (b := q 0) (c := q 2) (d := q 3)
    (fun he ↦ hx (he.symm ▸ (q.mem_support _).mpr ⟨2, rfl⟩))
    (q.injective.ne (by decide : (0 : Fin 4) ≠ 3)) h0 hdiag.1 (q.adjacent 2) h3.symm
  have hdegree : degreeIn G (q 1) q.support = 2 := by
    rw [q.degreeIn_eq]
    change 2 + (if G.Adj (q 1) (q 3) then 1 else 0) = 2
    rw [if_neg hdiag.2, add_zero]
  have hxdegree : degreeIn G x q.support = 2 := by
    rw [q.degree_eq_mask x 9 hrow]
    decide +kernel
  have hm : q 1 ∈ q.support := (q.mem_support _).mpr ⟨1, rfl⟩
  have he := degreeIn_erase_add G x (q 1) hm
  rw [hxdegree, if_neg hn1, add_zero] at he
  have hscore := edgeCount_replace G (q 1) x hm hx
  refine ⟨?_, ?_⟩
  · simpa only [erase_one_support] using hquad
  · rw [hdegree, he] at hscore
    omega

variable [Fintype V]

theorem exists_first_swap {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q 1 ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 1))} := by
  have hx : p.leaf ∉ q.support := by
    rw [hq]
    exact (c.presentPaw p hp).terminal_not_mem_block hs
  obtain ⟨hr, he⟩ := leaf_replacement q p.leaf hx hdiag hrow
  rw [hq] at hr he
  exact (hc.presentPaw_feasible p hp).exists_terminal_swap hs
    (hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩) hr he

theorem first_core_degree_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b))) : degreeIn G (q 1) (p.triangle ∪ b) ≤ 1 := by
  obtain ⟨d, _, ht, hT, _, _, hblocks⟩ := exists_first_swap hc p hp hs q hq hdiag hrow
  have hbd : b ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hbs, hb⟩)
  have hq1 : q 1 ∈ s := hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩
  have hout : q 1 ∉ p.triangle ∪ b := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · have hF : q 1 ∈ p.support := p.support_eq ▸ mem_insert_of_mem hh
      exact (mem_sdiff.mp (c.complementPartition.block_subset hs hq1)).2 (hp ▸ hF)
    · exact disjoint_left.mp (c.property.blocks_disjoint hs hb hbs.symm) hq1 hh
  by_contra! hh
  apply d.no_local_factor hcard hn hbd
  change LocalFactor G (insert d.terminal d.triangle ∪ b)
  rw [ht, hT, insert_union]
  exact hcore (q 1) hout (by omega)

theorem first_core_unique {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b)))
    (z : V) (hz : z ∈ b) (hz1 : G.Adj z (q 1)) :
    degreeIn G (q 1) (p.triangle ∪ b) = 1 ∧
      ∀ u ∈ p.triangle ∪ b, G.Adj (q 1) u ↔ u = z :=
  FullRow.unique_row_of_bound (p.triangle ∪ b) (q 1) z (mem_union_right _ hz) hz1.symm
    (first_core_degree_le_one hc hcard hn p hp hs q hq hdiag hrow hb hbs hcore)

omit [Fintype V] in
lemma second_neighbor_of_unique (q : Quadrilateral G) (K : Finset V) (z₁ z₂ : V)
    (hz₂ : z₂ ∈ K) (hne : z₁ ≠ z₂)
    (hunique : ∀ u ∈ K, G.Adj (q 1) u ↔ u = z₁)
    (hrow : 1 ≤ degreeIn G z₂ {q 1, q 2}) :
    ¬G.Adj z₂ (q 1) ∧ G.Adj z₂ (q 2) := by
  have hnot : ¬G.Adj z₂ (q 1) := fun hh ↦ hne ((hunique z₂ hz₂).mp hh.symm).symm
  refine ⟨hnot, ?_⟩
  obtain ⟨w, hw⟩ := card_pos.mp
    (show 0 < (({q 1, q 2} : Finset V).filter (G.Adj z₂)).card from hrow)
  obtain ⟨hw, hzw⟩ := mem_filter.mp hw
  rcases mem_insert.mp hw with rfl | hw
  · exact False.elim (hnot hzw)
  · exact (mem_singleton.mp hw) ▸ hzw

end Erdos577.TwoCore
