import ErdosProblems.Erdos577.CliqueCounts

/-! The minimum-degree count for any four-vertex remainder without a triangle. -/

namespace Erdos577.BlockPartition

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_heavy_block_of_four_remainder {r : Finset V} (hr : r.card = 4)
    (p : BlockPartition G (univ \ r)) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (ht : ¬TriangleIn G r) :
    ∃ b ∈ p.blocks, 9 ≤ contacts G r b := by
  have hq := p.no_quad_remainder hcard hn
  have he := four_set_edgeCount_le_three hr hq ht
  have hi := contacts_self_eq_twice_edgeCount G r
  have hpos : 1 ≤ k := by
    by_contra hh
    have hk : k = 0 := by omega
    exact hn (hk ▸ hasPacking_zero G)
  have hblocks := p.card
  rw [card_sdiff_of_subset (subset_univ _), card_univ, hr, hcard] at hblocks
  have hsum := minimum_degree_sum G r (2 * k) (fun v _ ↦ hdeg v)
  rw [hr] at hsum
  have hcover : r ∪ p.blocks.biUnion id = univ := by
    rw [p.cover, union_sdiff_self_eq_union, union_eq_right.mpr (subset_univ _)]
  have hd : Disjoint r (p.blocks.biUnion id) := by
    rw [p.cover]
    exact disjoint_sdiff_self_right
  rw [← hcover, contacts_union_right G _ hd,
    contacts_biUnion_right G _ _ _ p.disjoint] at hsum
  obtain ⟨b, hb, hheavy⟩ := exists_heavy_block G r p.blocks id 8 (by omega)
  exact ⟨b, hb, Nat.succ_le_of_lt hheavy⟩

end Erdos577.BlockPartition
