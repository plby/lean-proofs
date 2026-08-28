import ErdosProblems.Erdos577.Refinement
import ErdosProblems.Erdos577.BlockScores
import ErdosProblems.Erdos577.CopyCounts

/-! Exact score changes when a triangle remainder and one block are rearranged. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A local triangle remainder and one genuine quadrilateral partition the
specified vertex set. -/
structure LocalChain (G : SimpleGraph V) (s : Finset V) where
  terminal : V
  triangle : Finset V
  block : Finset V
  triangle_clique : G.IsNClique 3 triangle
  terminal_not_mem : terminal ∉ triangle
  quad : QuadOn G block
  disjoint : Disjoint (insert terminal triangle) block
  cover : insert terminal triangle ∪ block = s

namespace LocalChain

variable {s : Finset V}

def remainder (d : LocalChain G s) : Finset V := insert d.terminal d.triangle

lemma block_subset (d : LocalChain G s) : d.block ⊆ s := by
  exact subset_union_right.trans (le_of_eq d.cover)

lemma remainder_subset (d : LocalChain G s) : d.remainder ⊆ s := by
  exact subset_union_left.trans (le_of_eq d.cover)

lemma card_remainder (d : LocalChain G s) : d.remainder.card = 4 := by
  simp [remainder, d.terminal_not_mem, d.triangle_clique.card_eq]

lemma card (d : LocalChain G s) : s.card = 8 := by
  rw [← d.cover, card_union_of_disjoint d.disjoint, d.quad.card]
  have h := d.card_remainder
  change (insert d.terminal d.triangle).card = 4 at h
  omega

variable {W : Type*} [DecidableEq W] {H : SimpleGraph W}

/-- Copy all eight vertices and all required positive edges. Extra edges
in the receiving graph are permitted. -/
def image (d : LocalChain G s) (f : G.Copy H) : LocalChain H (s.image f) where
  terminal := f d.terminal
  triangle := d.triangle.image f
  block := d.block.image f
  triangle_clique := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
      exact f.toHom.map_rel'
        (d.triangle_clique.isClique hu hv (fun he ↦ hab (congrArg f he)))
    · have hinj : Function.Injective (f : V → W) := f.injective
      rw [card_image_of_injective _ hinj, d.triangle_clique.card_eq]
  terminal_not_mem := by
    intro h
    obtain ⟨v, hv, he⟩ := mem_image.mp h
    exact d.terminal_not_mem (f.injective he ▸ hv)
  quad := d.quad.image f
  disjoint := by
    have he : insert (f d.terminal) (d.triangle.image f) = d.remainder.image f := by
      simp only [remainder, image_insert]
    rw [he]
    apply disjoint_left.mpr
    intro v hv hr
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hv
    obtain ⟨b, hb, hab⟩ := mem_image.mp hr
    have he : b = a := f.injective hab
    exact (disjoint_left.mp d.disjoint) ha (he ▸ hb)
  cover := by
    simpa only [image_union, image_insert] using
      congrArg (fun u : Finset V ↦ u.image f) d.cover

lemma image_edgeCount_le [DecidableRel G.Adj] [DecidableRel H.Adj]
    (d : LocalChain G s) (f : G.Copy H) : edgeCount G d.block ≤ edgeCount H (d.image f).block :=
  edgeCount_image_le f d.block

lemma image_attachment_le [DecidableRel G.Adj] [DecidableRel H.Adj]
    (d : LocalChain G s) (f : G.Copy H) :
    degreeIn G d.terminal d.triangle ≤ degreeIn H (d.image f).terminal (d.image f).triangle :=
  degreeIn_image_le f d.terminal d.triangle

end LocalChain

/-- An exchange either strictly increases the block edge count or preserves
that count while exposing an attached terminal. Both conditions are positive. -/
def LocalImprovement [DecidableRel G.Adj] (s : Finset V) (oldEdges : ℕ) : Prop :=
  ∃ d : LocalChain G s, oldEdges ≤ edgeCount G d.block ∧
    (oldEdges < edgeCount G d.block ∨ 0 < degreeIn G d.terminal d.triangle)

lemma LocalImprovement.image {W : Type*} [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {s : Finset V} {oldEdges : ℕ}
    (h : LocalImprovement (G := G) s oldEdges) (f : G.Copy H) :
    LocalImprovement (G := H) (s.image f) oldEdges := by
  obtain ⟨d, hd, hgain⟩ := h
  refine ⟨d.image f, hd.trans (d.image_edgeCount_le f), ?_⟩
  rcases hgain with hgain | hatt
  · exact Or.inl (hgain.trans_le (d.image_edgeCount_le f))
  · exact Or.inr (hatt.trans_le (d.image_attachment_le f))

namespace TriangleChain

variable [Fintype V]

lemma replacement_disjoint (c : TriangleChain G) {b : Finset V}
    (d : LocalChain G (c.remainder ∪ b)) : Disjoint ((univ \ c.remainder) \ b) d.block := by
  apply disjoint_left.mpr
  intro v hv hd
  rcases mem_union.mp (d.block_subset hd) with hr | hb
  · exact (mem_sdiff.mp (mem_sdiff.mp hv).1).2 hr
  · exact (mem_sdiff.mp hv).2 hb

lemma replacement_cover (c : TriangleChain G) {b : Finset V}
    (d : LocalChain G (c.remainder ∪ b)) :
    ((univ \ c.remainder) \ b) ∪ d.block = univ \ d.remainder := by
  ext v
  have hc : (v ∈ d.remainder ∨ v ∈ d.block) ↔ (v ∈ c.remainder ∨ v ∈ b) := by
    rw [← mem_union, ← mem_union]
    exact congrArg (fun s ↦ v ∈ s) d.cover |>.to_iff
  have hd : ¬(v ∈ d.remainder ∧ v ∈ d.block) :=
    fun h ↦ (disjoint_left.mp d.disjoint) h.1 h.2
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  tauto

/-- The local rearrangement retains all blocks except the designated one. -/
def replaceBlock (c : TriangleChain G) (b : Finset V) (hb : b ∈ c.blocks)
    (d : LocalChain G (c.remainder ∪ b)) : TriangleChain G :=
  ofPartition d.triangle_clique d.terminal_not_mem {
    blocks := (c.blocks.erase b) ∪ {d.block}
    disjoint := ((c.complementPartition.remove b hb).union (BlockPartition.single d.quad)
      (c.replacement_disjoint d)).disjoint
    cover := by
      have h := ((c.complementPartition.remove b hb).union (BlockPartition.single d.quad)
        (c.replacement_disjoint d)).cover
      change ((c.blocks.erase b) ∪ {d.block}).biUnion id = _ at h
      rw [c.replacement_cover d] at h
      exact h
    quad := ((c.complementPartition.remove b hb).union (BlockPartition.single d.quad)
      (c.replacement_disjoint d)).quad }

@[simp] lemma replaceBlock_terminal (c : TriangleChain G) (b : Finset V) (hb : b ∈ c.blocks)
    (d : LocalChain G (c.remainder ∪ b)) : (c.replaceBlock b hb d).terminal = d.terminal := rfl

@[simp] lemma replaceBlock_triangle (c : TriangleChain G) (b : Finset V) (hb : b ∈ c.blocks)
    (d : LocalChain G (c.remainder ∪ b)) : (c.replaceBlock b hb d).triangle = d.triangle := rfl

@[simp] lemma replaceBlock_blocks (c : TriangleChain G) (b : Finset V) (hb : b ∈ c.blocks)
    (d : LocalChain G (c.remainder ∪ b)) :
    (c.replaceBlock b hb d).blocks = (c.blocks.erase b) ∪ {d.block} := rfl

variable [DecidableRel G.Adj]

lemma replaceBlock_edgeScore (c : TriangleChain G) (b : Finset V) (hb : b ∈ c.blocks)
    (d : LocalChain G (c.remainder ∪ b)) :
    (c.replaceBlock b hb d).edgeScore + edgeCount G b = c.edgeScore + edgeCount G d.block := by
  exact c.complementPartition.weightSum_replace_add b hb d.quad
    (c.replacement_disjoint d) (edgeCount G)

lemma completeScore_eq_sum (c : TriangleChain G) :
    c.completeScore = ∑ b ∈ c.blocks, if edgeCount G b = 6 then 1 else 0 := by
  rw [completeScore, card_eq_sum_ones, sum_filter]

lemma replaceBlock_completeScore (c : TriangleChain G) (b : Finset V) (hb : b ∈ c.blocks)
    (d : LocalChain G (c.remainder ∪ b)) :
    (c.replaceBlock b hb d).completeScore + (if edgeCount G b = 6 then 1 else 0) =
      c.completeScore + (if edgeCount G d.block = 6 then 1 else 0) := by
  rw [completeScore_eq_sum, completeScore_eq_sum]
  exact c.complementPartition.weightSum_replace_add b hb d.quad
    (c.replacement_disjoint d) (fun q ↦ if edgeCount G q = 6 then 1 else 0)

lemma Feasible.local_edges_le {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (d : LocalChain G (c.remainder ∪ b)) :
    edgeCount G d.block ≤ edgeCount G b := by
  have he := c.replaceBlock_edgeScore b hb d
  have hm := hc.edge_max (c.replaceBlock b hb d)
  omega

lemma replaceBlock_scores_eq (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks)
    (d : LocalChain G (c.remainder ∪ b)) (he : edgeCount G d.block = edgeCount G b) :
    (c.replaceBlock b hb d).edgeScore = c.edgeScore ∧
      (c.replaceBlock b hb d).completeScore = c.completeScore := by
  have h₁ := c.replaceBlock_edgeScore b hb d
  have h₂ := c.replaceBlock_completeScore b hb d
  rw [he] at h₁ h₂
  exact ⟨Nat.add_right_cancel h₁, Nat.add_right_cancel h₂⟩

lemma Refined.local_attachment_le {c : TriangleChain G} (hc : c.Refined)
    {b : Finset V} (hb : b ∈ c.blocks) (d : LocalChain G (c.remainder ∪ b))
    (he : edgeCount G d.block = edgeCount G b) :
    degreeIn G d.terminal d.triangle ≤ c.attachmentScore := by
  have hs := c.replaceBlock_scores_eq hb d he
  exact hc.attachment_max (c.replaceBlock b hb d) hs.1 hs.2

lemma Feasible.replaceBlock_feasible {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (d : LocalChain G (c.remainder ∪ b))
    (he : edgeCount G d.block = edgeCount G b) : (c.replaceBlock b hb d).Feasible := by
  have hs := c.replaceBlock_scores_eq hb d he
  constructor
  · intro e
    rw [hs.1]
    exact hc.edge_max e
  · intro e hed
    rw [hs.2]
    exact hc.complete_max e (hed.trans hs.1)

lemma Refined.no_local_improvement {c : TriangleChain G} (hc : c.Refined)
    (ha : c.attachmentScore = 0) {b : Finset V} (hb : b ∈ c.blocks) :
    ¬LocalImprovement (G := G) (c.remainder ∪ b) (edgeCount G b) := by
  rintro ⟨d, hd, hgain⟩
  have hle := hc.toFeasible.local_edges_le hb d
  have he : edgeCount G d.block = edgeCount G b := Nat.le_antisymm hle hd
  rcases hgain with hgain | hatt
  · omega
  · have hl := hc.local_attachment_le hb d he
    rw [ha] at hl
    omega

end TriangleChain

end Erdos577
