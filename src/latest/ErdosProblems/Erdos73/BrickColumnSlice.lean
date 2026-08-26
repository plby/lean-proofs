import ErdosProblems.Erdos73.BrickWallFaceUnion
import ErdosProblems.Erdos73.BrickColumnBlocks
import ErdosProblems.Erdos73.SubdivisionComposition
import ErdosProblems.Erdos73.RegularSubwalls

/-! A consecutive face-column block is exactly a translated elementary-wall subdivision. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {c r : ℕ}

def brickColumnSliceCopy (a d : ℕ) (hc : a + (d + 1) ≤ c) :
    (elementaryWall (d + 1) r).Copy (elementaryWall c r) :=
  elementaryWallCopyOfOffsets 0 a (by omega) hc

theorem brickFaceCopyAt_translate (a d : ℕ) (hc : a + (d + 1) ≤ c)
    (b : Fin (r - 1)) (j : Fin d) :
    (brickColumnSliceCopy a d hc).comp (brickFaceCopyAt (b, j)) =
      brickFaceCopyAt (b, brickBlockColumnIndex a d (by omega) j) := by
  apply Copy.ext
  intro l
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    change 2 * 0 + (b.val + (brickFacePosition l).1) = b.val + (brickFacePosition l).1
    omega
  · apply Fin.ext
    change 2 * a + (brickFaceColumn b.val j.val + (brickFacePosition l).2) =
      brickFaceColumn b.val (a + j.val) + (brickFacePosition l).2
    dsimp only [brickFaceColumn]
    omega

variable {V : Type*} {G : SimpleGraph V}

theorem brickFaceRegion_translate (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (hc : a + (d + 1) ≤ c) (b : Fin (r - 1)) (j : Fin d) :
    brickFaceRegion (S.restrictCopy (brickColumnSliceCopy a d hc)) (b, j) =
      brickFaceRegion S (b, brickBlockColumnIndex a d (by omega) j) := by
  change ((S.restrictCopy (brickColumnSliceCopy a d hc)).restrictCopy
    (brickFaceCopyAt (b, j))).vertexSet =
      (S.restrictCopy (brickFaceCopyAt (b, brickBlockColumnIndex a d (by omega) j))).vertexSet
  rw [S.restrictCopy_comp_vertexSet, brickFaceCopyAt_translate]

theorem brickFaceEdgeGraph_translate (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (hc : a + (d + 1) ≤ c) (b : Fin (r - 1)) (j : Fin d) :
    brickFaceEdgeGraph (S.restrictCopy (brickColumnSliceCopy a d hc)) (b, j) =
      brickFaceEdgeGraph S (b, brickBlockColumnIndex a d (by omega) j) := by
  change ((S.restrictCopy (brickColumnSliceCopy a d hc)).restrictCopy
    (brickFaceCopyAt (b, j))).actualEdgeGraph =
      (S.restrictCopy (brickFaceCopyAt (b, brickBlockColumnIndex a d (by omega) j))).actualEdgeGraph
  rw [S.restrictCopy_comp_actualEdgeGraph, brickFaceCopyAt_translate]

theorem brickColumnSlice_vertexSet (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (hc : a + (d + 1) ≤ c) (hr : 2 ≤ r) (hd : 0 < d) :
    (S.restrictCopy (brickColumnSliceCopy a d hc)).vertexSet =
      brickColumnBlock S a d (by omega) := by
  rw [brickWall_vertexSet_eq_faceUnion _ (by omega : 2 ≤ d + 1) hr]
  ext x
  constructor
  · intro hx
    obtain ⟨⟨b, j⟩, _, hx⟩ := mem_biUnion.mp hx
    rw [brickFaceRegion_translate] at hx
    exact mem_biUnion.mpr ⟨j, mem_univ _, mem_biUnion.mpr ⟨b, mem_univ _, hx⟩⟩
  · intro hx
    obtain ⟨j, _, hx⟩ := mem_biUnion.mp hx
    obtain ⟨b, _, hx⟩ := mem_biUnion.mp hx
    refine mem_biUnion.mpr ⟨(b, j), mem_univ _, ?_⟩
    rw [brickFaceRegion_translate]
    exact hx

theorem brickColumnSlice_actualEdgeGraph (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (hc : a + (d + 1) ≤ c) (hr : 2 ≤ r) (hd : 0 < d) :
    (S.restrictCopy (brickColumnSliceCopy a d hc)).actualEdgeGraph =
      brickColumnBlockGraph S a d (by omega) := by
  rw [brickWall_actualEdgeGraph_eq_faceUnion _ (by omega : 2 ≤ d + 1) hr]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨b, j⟩
    rw [brickFaceEdgeGraph_translate]
    exact le_iSup_of_le j (le_iSup (fun b =>
      brickFaceEdgeGraph S (b, brickBlockColumnIndex a d (by omega) j)) b)
  · apply iSup_le
    intro j
    apply iSup_le
    intro b
    rw [← brickFaceEdgeGraph_translate S a d hc b j]
    exact le_iSup (fun i => brickFaceEdgeGraph
      (S.restrictCopy (brickColumnSliceCopy a d hc)) i) (b, j)

end
end Erdos73
