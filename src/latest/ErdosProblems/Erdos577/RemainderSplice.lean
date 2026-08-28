import ErdosProblems.Erdos577.BlockScores

/-! Replace the remainder and one block by a specified new remainder and its cyclic complement. -/

namespace Erdos577.BlockPartition

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {r b u : Finset V}

lemma remainder_splice_disjoint (_p : BlockPartition G (univ \ r)) :
    Disjoint ((univ \ r) \ b) ((r ∪ b) \ u) := by
  apply disjoint_left.mpr
  intro v hv hu
  rcases mem_union.mp (mem_sdiff.mp hu).1 with hr | hb
  · exact (mem_sdiff.mp (mem_sdiff.mp hv).1).2 hr
  · exact (mem_sdiff.mp hv).2 hb

lemma remainder_splice_cover (_p : BlockPartition G (univ \ r)) (hu : u ⊆ r ∪ b) :
    ((univ \ r) \ b) ∪ ((r ∪ b) \ u) = univ \ u := by
  ext v
  have h : v ∈ u → v ∈ r ∨ v ∈ b := fun h ↦ mem_union.mp (hu h)
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  tauto

def replaceRemainder (p : BlockPartition G (univ \ r)) (b : Finset V) (hb : b ∈ p.blocks)
    (u : Finset V) (hu : u ⊆ r ∪ b) (hq : QuadOn G ((r ∪ b) \ u)) :
    BlockPartition G (univ \ u) where
  blocks := p.blocks.erase b ∪ {(r ∪ b) \ u}
  disjoint := ((p.remove b hb).union (single hq) p.remainder_splice_disjoint).disjoint
  cover := ((p.remove b hb).union (single hq) p.remainder_splice_disjoint).cover.trans
    (p.remainder_splice_cover hu)
  quad := ((p.remove b hb).union (single hq) p.remainder_splice_disjoint).quad

lemma weightSum_replaceRemainder_add (p : BlockPartition G (univ \ r)) (b : Finset V)
    (hb : b ∈ p.blocks) (u : Finset V) (hu : u ⊆ r ∪ b) (hq : QuadOn G ((r ∪ b) \ u))
    (w : Finset V → ℕ) :
    (p.replaceRemainder b hb u hu hq).weightSum w + w b = p.weightSum w + w ((r ∪ b) \ u) :=
  p.weightSum_replace_add b hb hq p.remainder_splice_disjoint w

end Erdos577.BlockPartition
