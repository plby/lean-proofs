import ErdosProblems.Erdos577.TwoCoreInside
import ErdosProblems.Erdos577.OutsideSelectedCount

/-! Outside averaging and the actual two-block splice exposing the scored path. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_outside {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hd : Disjoint p.support q.support)
    (h3 : G.Adj p.leaf (q 3))
    (hinside : contacts G (insert (q 3) (FullRow.pathTriple p))
      (p.support ∪ (b ∪ q.support)) ≤ 23) :
    ∃ j ∈ c.blocks, j ≠ b ∧ j ≠ s ∧
      9 ≤ contacts G (exposedPath p q hd h3).support j := by
  have hsel : ({b, s} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hb (singleton_subset_iff.mpr hs)
  have hsize : ({b, s} : Finset (Finset V)).card = 2 := card_pair_eq_two_iff.mpr hbs
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hsel
  have hge := card_le_card hsel
  have hcore : c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id =
      p.support ∪ (b ∪ q.support) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hp, hq]
  obtain ⟨j, hj, hjn, hh⟩ := c.exists_heavy_outside_selected {b, s} hsel
    (exposedPath p q hd h3).support (2 * k) 8 hdeg (by
      rw [FourPath.card_support, hcore, exposedPath_support]
      omega)
  exact ⟨j, hj, (fun he ↦ hjn (mem_insert.mpr (Or.inl he))),
    (fun he ↦ hjn (mem_insert_of_mem (mem_singleton.mpr he))), Nat.succ_le_of_lt hh⟩

theorem exists_path_partition {c : TriangleChain G}
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hd : Disjoint p.support q.support)
    (h3 : G.Adj p.leaf (q 3)) (z : V) (hz : z ∈ b)
    (hBrep : QuadOn G (insert (p.vertices 3) (b.erase z)))
    (hBscore : edgeCount G (insert (p.vertices 3) (b.erase z)) = edgeCount G b)
    (hQrep : QuadOn G (insert z (q.support.erase (q 3))))
    (hQscore : edgeCount G (insert z (q.support.erase (q 3))) = edgeCount G q.support + 1) :
    ∃ parts : BlockPartition G (univ \ (exposedPath p q hd h3).support),
      parts.weightSum (edgeCount G) = c.edgeScore + 1 ∧
      ∀ j ∈ c.blocks, j ≠ b → j ≠ s → j ∈ parts.blocks := by
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hQB : Disjoint q.support b := by
    rw [hq]
    exact c.property.blocks_disjoint hs hb hbs.symm
  let localParts := (BlockPartition.single hBrep).union (BlockPartition.single hQrep)
    (replacement_blocks_disjoint p q hd b hpB hQB z hz)
  have hsel : ({b, s} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hb (singleton_subset_iff.mpr hs)
  have hcore : c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id =
      p.support ∪ (b ∪ q.support) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hp, hq]
  have hsub : insert (p.vertices 3) (b.erase z) ∪ insert z (q.support.erase (q 3)) ⊆
      c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id := by
    rw [hcore]
    exact replacement_subset p q b hQB z hz
  have hrem : (c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id) \
      (insert (p.vertices 3) (b.erase z) ∪ insert z (q.support.erase (q 3))) =
        (exposedPath p q hd h3).support := by
    rw [hcore]
    exact replacement_remainder p q hd b hpB hQB z hz h3
  let raw := c.complementPartition.splice {b, s} hsel localParts hsub
  let parts : BlockPartition G (univ \ (exposedPath p q hd h3).support) := {
    blocks := raw.blocks
    disjoint := raw.disjoint
    cover := raw.cover.trans (congrArg (fun r ↦ univ \ r) hrem)
    quad := raw.quad }
  have hlocal : localParts.weightSum (edgeCount G) = edgeCount G b + edgeCount G s + 1 := by
    rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
      BlockPartition.weightSum_single, hBscore, hQscore, hq]
    omega
  have hold : (c.complementPartition.select {b, s} hsel).weightSum (edgeCount G) =
      edgeCount G b + edgeCount G s := sum_pair hbs
  have hsum := c.complementPartition.weightSum_splice_add {b, s} hsel localParts hsub
    (edgeCount G)
  rw [hold, hlocal] at hsum
  change parts.weightSum (edgeCount G) + (edgeCount G b + edgeCount G s) =
    c.edgeScore + (edgeCount G b + edgeCount G s + 1) at hsum
  refine ⟨parts, by omega, ?_⟩
  intro j hj hjb hjs
  change j ∈ (c.blocks \ {b, s}) ∪ localParts.blocks
  exact mem_union_left _ (mem_sdiff.mpr ⟨hj, by
    simp only [mem_insert, mem_singleton]
    exact not_or.mpr ⟨hjb, hjs⟩⟩)

end Erdos577.TwoCore
