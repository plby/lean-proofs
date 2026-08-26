import ErdosProblems.Erdos73.SubdivisionEdgeGraph
import ErdosProblems.Erdos73.CrossFamilyRobust

/-! Strip networks use their actual face edges, without induced-graph shortcuts. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

def brickFaceEdgeGraph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) : SimpleGraph V :=
  (S.restrictCopy (elementaryBrickFaceCopy i.1.val (brickFaceColumn i.1.val i.2.val)
    (by have hi := i.1.isLt; omega)
    (by have hi := i.2.isLt; unfold brickFaceColumn; omega)
    (by unfold brickFaceColumn; omega))).actualEdgeGraph

theorem brickFaceEdgeGraph_le (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) : brickFaceEdgeGraph S i ≤ S.actualEdgeGraph :=
  S.restrictCopy_actualEdgeGraph_le _

theorem brickFaceEdgeGraph_adj_support (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) {x y : V} (hxy : (brickFaceEdgeGraph S i).Adj x y) :
    x ∈ brickFaceRegion S i ∧ y ∈ brickFaceRegion S i :=
  GraphSubdivisionModel.actualEdgeGraph_adj_support _ hxy

theorem brickFaceRegion_robust_in_graph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) (J : SimpleGraph V) (hJ : brickFaceEdgeGraph S i ≤ J) :
    DeletionOneConnected J (brickFaceRegion S i) := by
  let T := S.restrictCopy (elementaryBrickFaceCopy i.1.val (brickFaceColumn i.1.val i.2.val)
    (by have hi := i.1.isLt; omega)
    (by have hi := i.2.isLt; unfold brickFaceColumn; omega)
    (by unfold brickFaceColumn; omega))
  have hh := hexagonSubdivision_deletionOneConnected (T.transferTo J hJ)
  have he : (T.transferTo J hJ).vertexSet = brickFaceRegion S i := by
    ext x
    simp only [GraphSubdivisionModel.mem_vertexSet, GraphSubdivisionModel.transferTo,
      Erdos73Infrastructure.SimpleGraph.GraphPath.transfer_vertexSet, brickFaceRegion,
      brickFaceSupport, T]
  exact he ▸ hh

theorem brickFaceRowStrip_robust_in_graph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (hc : 2 ≤ c) (a : Fin (r - 1)) (J : SimpleGraph V)
    (hJ : ∀ j, DeletionOneConnected J (brickFaceRegion S (a, j))) :
    DeletionOneConnected J (brickFaceRowStrip S a) := by
  have : NeZero (c - 1) := ⟨by omega⟩
  apply deletionOneConnected_biUnion (fun j => brickFaceRegion S (a, j)) hJ
    (show (pathGraph (c - 1)).Connected from ⟨pathGraph_preconnected _⟩)
  intro i j hij
  rcases pathGraph_adj.mp hij with hij | hij
  · exact brickFaceRegion_horizontal_overlap S a i j hij
  · rw [inter_comm]
    exact brickFaceRegion_horizontal_overlap S a j i hij

theorem brickFaceColumnStrip_robust_in_graph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (hr : 2 ≤ r) (j : Fin (c - 1)) (J : SimpleGraph V)
    (hJ : ∀ a, DeletionOneConnected J (brickFaceRegion S (a, j))) :
    DeletionOneConnected J (brickFaceColumnStrip S j) := by
  have : NeZero (r - 1) := ⟨by omega⟩
  apply deletionOneConnected_biUnion (fun a => brickFaceRegion S (a, j)) hJ
    (show (pathGraph (r - 1)).Connected from ⟨pathGraph_preconnected _⟩)
  intro a b hab
  rcases pathGraph_adj.mp hab with hab | hab
  · exact brickFaceRegion_vertical_overlap S a b j hab
  · rw [inter_comm]
    exact brickFaceRegion_vertical_overlap S b a j hab

theorem brickStripNetwork_robust_in_graph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1)))
    (hA : A.Nonempty) (hB : B.Nonempty) (J : SimpleGraph V)
    (hJ : ∀ i, i.1 ∈ A ∨ i.2 ∈ B → DeletionOneConnected J (brickFaceRegion S i)) :
    DeletionOneConnected J (brickStripNetwork S A B) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hr : 2 ≤ r := by have hh := a.isLt; omega
  have hc : 2 ≤ c := by have hh := b.isLt; omega
  exact deletionOneConnected_twoFamilyUnion A B (brickFaceRowStrip S) (brickFaceColumnStrip S)
    ⟨a, ha⟩ ⟨b, hb⟩
    (fun a ha => brickFaceRowStrip_robust_in_graph S hc a J (fun j => hJ (a, j) (Or.inl ha)))
    (fun b hb => brickFaceColumnStrip_robust_in_graph S hr b J (fun a => hJ (a, b) (Or.inr hb)))
    (fun a _ b _ => brickFaceRowColumnStrip_overlap S a b)

def brickStripNetworkGraph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) : SimpleGraph V :=
  ⨆ i : Fin (r - 1) × Fin (c - 1), ⨆ (_ : i.1 ∈ A ∨ i.2 ∈ B), brickFaceEdgeGraph S i

theorem brickStripNetworkGraph_le (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) :
    brickStripNetworkGraph S A B ≤ S.actualEdgeGraph :=
  iSup_le fun i => iSup_le fun _ => brickFaceEdgeGraph_le S i

theorem brickFaceRegion_subset_network (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1)))
    (i : Fin (r - 1) × Fin (c - 1)) (hi : i.1 ∈ A ∨ i.2 ∈ B) :
    brickFaceRegion S i ⊆ brickStripNetwork S A B := by
  intro x hx
  apply (mem_brickStripNetwork S A B x).mpr
  rcases hi with hi | hi
  · exact Or.inl ⟨i.1, hi, mem_biUnion.mpr ⟨i.2, mem_univ _, hx⟩⟩
  · exact Or.inr ⟨i.2, hi, mem_biUnion.mpr ⟨i.1, mem_univ _, hx⟩⟩

theorem brickStripNetworkGraph_adj_support (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) {x y : V}
    (hxy : (brickStripNetworkGraph S A B).Adj x y) :
    x ∈ brickStripNetwork S A B ∧ y ∈ brickStripNetwork S A B := by
  obtain ⟨i, hxy⟩ := SimpleGraph.iSup_adj.mp hxy
  obtain ⟨hi, hxy⟩ := SimpleGraph.iSup_adj.mp hxy
  have hh := brickFaceEdgeGraph_adj_support S i hxy
  exact ⟨brickFaceRegion_subset_network S A B i hi hh.1,
    brickFaceRegion_subset_network S A B i hi hh.2⟩

theorem brickStripNetwork_robust_of_edges (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1)))
    (hA : A.Nonempty) (hB : B.Nonempty) (J : SimpleGraph V)
    (hJ : brickStripNetworkGraph S A B ≤ J) :
    DeletionOneConnected J (brickStripNetwork S A B) := by
  apply brickStripNetwork_robust_in_graph S A B hA hB J
  intro i hi
  apply brickFaceRegion_robust_in_graph S i J
  exact (le_iSup_of_le i (le_iSup (fun _ : i.1 ∈ A ∨ i.2 ∈ B =>
    brickFaceEdgeGraph S i) hi)).trans hJ

end
end Erdos73
