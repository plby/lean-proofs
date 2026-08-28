import ErdosProblems.Erdos577.BlockScores

/-! Selection and deletion of arbitrary finite families of cycle blocks. -/

namespace Erdos577.BlockPartition

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s : Finset V}

def select (p : BlockPartition G s) (bs : Finset (Finset V)) (hbs : bs ⊆ p.blocks) :
    BlockPartition G (bs.biUnion id) where
  blocks := bs
  disjoint := fun _ hb _ hc hbc ↦ p.disjoint (hbs hb) (hbs hc) hbc
  cover := rfl
  quad := fun b hb ↦ p.quad b (hbs hb)

def removeMany (p : BlockPartition G s) (bs : Finset (Finset V)) (hbs : bs ⊆ p.blocks) :
    BlockPartition G (s \ bs.biUnion id) where
  blocks := p.blocks \ bs
  disjoint := fun _ hb _ hc hbc ↦ p.disjoint (mem_sdiff.mp hb).1 (mem_sdiff.mp hc).1 hbc
  cover := by
    ext v
    simp only [mem_biUnion, mem_sdiff]
    constructor
    · rintro ⟨b, ⟨hb, hbn⟩, hv⟩
      refine ⟨p.block_subset hb hv, ?_⟩
      rintro ⟨a, ha, hva⟩
      have hba : b ≠ a := fun he ↦ hbn (he.symm ▸ ha)
      exact (disjoint_left.mp (p.disjoint hb (hbs ha) hba)) hv hva
    · rintro ⟨hv, hnot⟩
      rw [← p.cover] at hv
      obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp hv
      exact ⟨b, ⟨hb, fun h ↦ hnot ⟨b, h, hvb⟩⟩, hvb⟩
  quad := fun b hb ↦ p.quad b (mem_sdiff.mp hb).1

lemma weightSum_removeMany_add (p : BlockPartition G s) (bs : Finset (Finset V))
    (hbs : bs ⊆ p.blocks) (w : Finset V → ℕ) :
    (p.removeMany bs hbs).weightSum w + (p.select bs hbs).weightSum w = p.weightSum w := by
  exact sum_sdiff hbs

lemma selected_subset (p : BlockPartition G s) {bs : Finset (Finset V)} (hbs : bs ⊆ p.blocks) :
    bs.biUnion id ⊆ s := by
  intro v hv
  obtain ⟨b, hb, hv⟩ := mem_biUnion.mp hv
  exact p.block_subset (hbs hb) hv

variable [Fintype V] {r u : Finset V}

lemma splice_disjoint (_p : BlockPartition G (univ \ r)) {bs : Finset (Finset V)}
    (hu : u ⊆ r ∪ bs.biUnion id) : Disjoint ((univ \ r) \ bs.biUnion id) u := by
  apply disjoint_left.mpr
  intro v hv hvu
  rcases mem_union.mp (hu hvu) with hr | hbs
  · exact (mem_sdiff.mp (mem_sdiff.mp hv).1).2 hr
  · exact (mem_sdiff.mp hv).2 hbs

lemma splice_cover (_p : BlockPartition G (univ \ r)) {bs : Finset (Finset V)}
    (hu : u ⊆ r ∪ bs.biUnion id) :
    ((univ \ r) \ bs.biUnion id) ∪ u = univ \ ((r ∪ bs.biUnion id) \ u) := by
  ext v
  have hv : v ∈ u → v ∈ r ∨ v ∈ bs.biUnion id := fun h ↦ mem_union.mp (hu h)
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  tauto

/-- Keep all unselected blocks and cover the chosen local vertices except
for the new remainder. The blocks are explicit; no outside vertex is lost. -/
def splice (p : BlockPartition G (univ \ r)) (bs : Finset (Finset V)) (hbs : bs ⊆ p.blocks)
    (q : BlockPartition G u) (hu : u ⊆ r ∪ bs.biUnion id) :
    BlockPartition G (univ \ ((r ∪ bs.biUnion id) \ u)) where
  blocks := (p.blocks \ bs) ∪ q.blocks
  disjoint := ((p.removeMany bs hbs).union q (p.splice_disjoint hu)).disjoint
  cover := by
    have h := ((p.removeMany bs hbs).union q (p.splice_disjoint hu)).cover
    exact h.trans (p.splice_cover hu)
  quad := ((p.removeMany bs hbs).union q (p.splice_disjoint hu)).quad

lemma weightSum_splice_add (p : BlockPartition G (univ \ r)) (bs : Finset (Finset V))
    (hbs : bs ⊆ p.blocks) (q : BlockPartition G u) (hu : u ⊆ r ∪ bs.biUnion id)
    (w : Finset V → ℕ) :
    (p.splice bs hbs q hu).weightSum w + (p.select bs hbs).weightSum w =
      p.weightSum w + q.weightSum w := by
  have hsum := (p.removeMany bs hbs).weightSum_union q (p.splice_disjoint hu) w
  change (p.splice bs hbs q hu).weightSum w = _ at hsum
  rw [hsum]
  have h := p.weightSum_removeMany_add bs hbs w
  omega

end Erdos577.BlockPartition
