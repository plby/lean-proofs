import ErdosProblems.Erdos577.FiniteExchange

/-! Replacing a remainder and one cycle while retaining every untouched block. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace BlockPartition

/-- Remove one block, retaining a partition of exactly the other vertices. -/
def remove {s : Finset V} (p : BlockPartition G s) (q : Finset V) (hq : q ∈ p.blocks) :
    BlockPartition G (s \ q) where
  blocks := p.blocks.erase q
  disjoint := fun _ hb _ hc hbc ↦ p.disjoint (mem_erase.mp hb).2 (mem_erase.mp hc).2 hbc
  cover := by
    ext v
    simp only [mem_biUnion, mem_erase, mem_sdiff]
    constructor
    · rintro ⟨b, ⟨hbq, hb⟩, hv⟩
      exact ⟨p.block_subset hb hv, fun hvq ↦
        (disjoint_left.mp (p.disjoint hb hq hbq)) hv hvq⟩
    · rintro ⟨hv, hvq⟩
      rw [← p.cover] at hv
      obtain ⟨b, hb, hv⟩ := mem_biUnion.mp hv
      exact ⟨b, ⟨fun he ↦ hvq (he ▸ hv), hb⟩, hv⟩
  quad := fun b hb ↦ p.quad b (mem_erase.mp hb).2

variable [Fintype V]

/-- A local eight-vertex exchange extends to a triangle chain in a graph
without a quadrilateral factor. No outside block is discarded. -/
lemma chain_of_local_exchange {r : Finset V} (p : BlockPartition G (univ \ r))
    (hr : r.card = 4) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {q : Finset V} (hq : q ∈ p.blocks)
    (he : LocalExchange G (r ∪ q)) : Nonempty (TriangleChain G) := by
  obtain ⟨s, hs, hsq, hsrem⟩ := he
  have hrq : Disjoint r q := by
    apply disjoint_left.mpr
    intro v hvr hvq
    exact (mem_sdiff.mp (p.block_subset hq hvq)).2 hvr
  have hrest : Disjoint ((univ \ r) \ q) s := by
    apply disjoint_left.mpr
    intro v hv hvs
    rcases mem_union.mp (hs hvs) with hvr | hvq
    · exact (mem_sdiff.mp (mem_sdiff.mp hv).1).2 hvr
    · exact (mem_sdiff.mp hv).2 hvq
  have hcover : ((univ \ r) \ q) ∪ s = univ \ ((r ∪ q) \ s) := by
    ext v
    have hv : v ∈ s → v ∈ r ∨ v ∈ q := fun h ↦ mem_union.mp (hs h)
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    tauto
  have hp : BlockPartition G (univ \ ((r ∪ q) \ s)) :=
    hcover ▸ (p.remove q hq).union (single hsq) hrest
  have hc : ((r ∪ q) \ s).card = 4 := by
    rw [card_sdiff_of_subset hs, card_union_of_disjoint hrq, hr, (p.quad q hq).card, hsq.card]
  rcases hsrem with hsrem | hsrem
  · exact False.elim (hp.no_quad_remainder hcard hn hsrem)
  · exact TriangleChain.exists_of_triangle hc hp hsrem

end BlockPartition

end Erdos577
