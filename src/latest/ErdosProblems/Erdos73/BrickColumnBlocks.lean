import ErdosProblems.Erdos73.BrickNetworkEdges

/-! Consecutive blocks of actual face-column strips, with their exact edges. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

def brickBlockColumnIndex (a d : ℕ) (ha : a + d ≤ c - 1) (j : Fin d) : Fin (c - 1) :=
  ⟨a + j.val, by have hj := j.isLt; omega⟩

def brickColumnBlock (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) : Finset V :=
  Finset.univ.biUnion fun j : Fin d => brickFaceColumnStrip S (brickBlockColumnIndex a d ha j)

def brickColumnBlockGraph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) : SimpleGraph V :=
  ⨆ j : Fin d, ⨆ b : Fin (r - 1), brickFaceEdgeGraph S (b, brickBlockColumnIndex a d ha j)

theorem brickColumnBlock_subset (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) : brickColumnBlock S a d ha ⊆ S.vertexSet := by
  intro x hx
  obtain ⟨j, _, hx⟩ := mem_biUnion.mp hx
  exact brickFaceColumnStrip_subset S (brickBlockColumnIndex a d ha j) hx

theorem brickColumnBlockGraph_le (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) : brickColumnBlockGraph S a d ha ≤ S.actualEdgeGraph :=
  iSup_le fun j => iSup_le fun b => brickFaceEdgeGraph_le S (b, brickBlockColumnIndex a d ha j)

theorem brickColumnBlockGraph_adj_support (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) {x y : V}
    (hxy : (brickColumnBlockGraph S a d ha).Adj x y) :
    x ∈ brickColumnBlock S a d ha ∧ y ∈ brickColumnBlock S a d ha := by
  obtain ⟨j, hxy⟩ := SimpleGraph.iSup_adj.mp hxy
  obtain ⟨b, hxy⟩ := SimpleGraph.iSup_adj.mp hxy
  have hh := brickFaceEdgeGraph_adj_support S (b, brickBlockColumnIndex a d ha j) hxy
  exact ⟨mem_biUnion.mpr ⟨j, mem_univ _, mem_biUnion.mpr ⟨b, mem_univ _, hh.1⟩⟩,
    mem_biUnion.mpr ⟨j, mem_univ _, mem_biUnion.mpr ⟨b, mem_univ _, hh.2⟩⟩⟩

theorem brickFaceColumnStrip_adj_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (hr : 2 ≤ r) (i j : Fin (c - 1)) (hij : i.val + 1 = j.val) :
    2 ≤ (brickFaceColumnStrip S i ∩ brickFaceColumnStrip S j).card := by
  let b : Fin (r - 1) := ⟨0, by omega⟩
  apply (brickFaceRegion_horizontal_overlap S b i j hij).trans
  apply card_le_card
  intro x hx
  exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨b, mem_univ _, (mem_inter.mp hx).1⟩,
    mem_biUnion.mpr ⟨b, mem_univ _, (mem_inter.mp hx).2⟩⟩

theorem brickColumnBlock_robust_of_edges (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) (hr : 2 ≤ r) (hd : 0 < d) (J : SimpleGraph V)
    (hJ : brickColumnBlockGraph S a d ha ≤ J) :
    DeletionOneConnected J (brickColumnBlock S a d ha) := by
  have : NeZero d := ⟨by omega⟩
  have hcol (j : Fin d) :
      DeletionOneConnected J (brickFaceColumnStrip S (brickBlockColumnIndex a d ha j)) := by
    apply brickFaceColumnStrip_robust_in_graph S hr _ J
    intro b
    apply brickFaceRegion_robust_in_graph S _ J
    exact (le_iSup_of_le j (le_iSup (fun b : Fin (r - 1) =>
      brickFaceEdgeGraph S (b, brickBlockColumnIndex a d ha j)) b)).trans hJ
  apply deletionOneConnected_biUnion
    (fun j : Fin d => brickFaceColumnStrip S (brickBlockColumnIndex a d ha j)) hcol
    (show (pathGraph d).Connected from ⟨pathGraph_preconnected _⟩)
  intro i j hij
  rcases pathGraph_adj.mp hij with hij | hij
  · apply brickFaceColumnStrip_adj_overlap S hr
    change a + i.val + 1 = a + j.val
    omega
  · rw [inter_comm]
    apply brickFaceColumnStrip_adj_overlap S hr
    change a + j.val + 1 = a + i.val
    omega

theorem brickRowStrip_block_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) (hd : 0 < d) (b : Fin (r - 1)) :
    2 ≤ (brickFaceRowStrip S b ∩ brickColumnBlock S a d ha).card := by
  let j : Fin d := ⟨0, hd⟩
  let k := brickBlockColumnIndex a d ha j
  apply (brickFaceRegion_robust S (b, k)).two_le_card.trans
  apply card_le_card
  intro x hx
  exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨k, mem_univ _, hx⟩,
    mem_biUnion.mpr ⟨j, mem_univ _, mem_biUnion.mpr ⟨b, mem_univ _, hx⟩⟩⟩

theorem brickStripNetwork_block_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) (hA : A.Nonempty)
    (a d : ℕ) (ha : a + d ≤ c - 1) (hd : 0 < d) :
    2 ≤ (brickStripNetwork S A B ∩ brickColumnBlock S a d ha).card := by
  obtain ⟨b, hb⟩ := hA
  apply (brickRowStrip_block_overlap S a d ha hd b).trans
  apply card_le_card
  apply inter_subset_inter _ subset_rfl
  intro x hx
  exact (mem_brickStripNetwork S A B x).mpr (Or.inl ⟨b, hb, hx⟩)

end
end Erdos73
